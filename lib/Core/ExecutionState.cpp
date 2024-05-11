//===-- ExecutionState.cpp ------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "ExecutionState.h"

#include "Memory.h"

#include "klee/Expr/Expr.h"
#include "klee/Module/Cell.h"
#include "klee/Module/InstructionInfoTable.h"
#include "klee/Module/KInstruction.h"
#include "klee/Module/KModule.h"
#include "klee/Support/Casting.h"
#include "klee/Support/OptionCategories.h"

#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instructions.h"

#include <cassert>
#include <iomanip>
#include <map>
#include <set>
#include <string>
#include <regex>
#include <sstream>
#include <stdarg.h>

using namespace llvm;
using namespace klee;

namespace {
cl::opt<bool> DebugLogStateMerge(
    "debug-log-state-merge", cl::init(false),
    cl::desc("Debug information for underlying state merging (default=false)"),
    cl::cat(MergeCat));
  
}
namespace klee {
  extern cl::opt<bool> SingleObjectResolution; 
}

/***/

std::uint32_t ExecutionState::nextID = 1;

/***/

StackFrame::StackFrame(KInstIterator _caller, KFunction *_kf)
  : caller(_caller), kf(_kf), callPathNode(0), 
    minDistToUncoveredOnReturn(0), varargs(0) {
  locals = new Cell[kf->numRegisters];
}

StackFrame::StackFrame(const StackFrame &s) 
  : caller(s.caller),
    kf(s.kf),
    callPathNode(s.callPathNode),
    allocas(s.allocas),
    minDistToUncoveredOnReturn(s.minDistToUncoveredOnReturn),
    varargs(s.varargs) {
  locals = new Cell[s.kf->numRegisters];
  for (unsigned i=0; i<s.kf->numRegisters; i++)
    locals[i] = s.locals[i];
}

StackFrame::~StackFrame() { 
  delete[] locals; 
}

/***/

ExecutionState::ExecutionState(KFunction *kf, MemoryManager *mm)
    : pc(kf->instructions), prevPC(pc) {
  pushFrame(nullptr, kf);
  setID();
  if (mm->stackFactory && mm->heapFactory) {
    stackAllocator = mm->stackFactory.makeAllocator();
    heapAllocator = mm->heapFactory.makeAllocator();
  }
}

ExecutionState::~ExecutionState() {
  for (const auto &cur_mergehandler: openMergeStack){
    cur_mergehandler->removeOpenState(this);
  }

  while (!stack.empty()) popFrame();
}

ExecutionState::ExecutionState(const ExecutionState& state):
    pc(state.pc),
    prevPC(state.prevPC),
    stack(state.stack),
    incomingBBIndex(state.incomingBBIndex),
    depth(state.depth),
    addressSpace(state.addressSpace),
    stackAllocator(state.stackAllocator),
    heapAllocator(state.heapAllocator),
    constraints(state.constraints),
    pathOS(state.pathOS),
    symPathOS(state.symPathOS),
    coveredLines(state.coveredLines),
    symbolics(state.symbolics),
    cexPreferences(state.cexPreferences),
    arrayNames(state.arrayNames),
    openMergeStack(state.openMergeStack),
    steppedInstructions(state.steppedInstructions),
    instsSinceCovNew(state.instsSinceCovNew),
    unwindingInformation(state.unwindingInformation
                             ? state.unwindingInformation->clone()
                             : nullptr),
    coveredNew(state.coveredNew),
    forkDisabled(state.forkDisabled),
    base_addrs(state.base_addrs),
    base_mos(state.base_mos),
    readSet(state.readSet),
    writeSet(state.writeSet),
    referencesToArg(state.referencesToArg),
    argContents(state.argContents),
    referencesToMapReturn(state.referencesToMapReturn),
    mapCallStrings(state.mapCallStrings),
    branchesOnMapReturnReference(state.branchesOnMapReturnReference) {
  for (const auto &cur_mergehandler: openMergeStack)
    cur_mergehandler->addOpenState(this);
}

ExecutionState *ExecutionState::branch() {
  depth++;

  auto *falseState = new ExecutionState(*this);
  falseState->setID();
  falseState->coveredNew = false;
  falseState->coveredLines.clear();

  return falseState;
}

void ExecutionState::addRead(std::string newRead) {
  readSet.insert(newRead);
}

void ExecutionState::addReferenceToArg(llvm::Value *val) {
  referencesToArg.insert(val);
}

bool ExecutionState::isReferenceToArg(llvm::Value *val) {
  return referencesToArg.find(val) != referencesToArg.end();
}

void ExecutionState::printReferences() {
  llvm::errs() << "References to the arguments:\n";
  llvm::errs() << "{ ";
  for (auto const& reference : referencesToArg) {
    reference->dump();
  }
  llvm::errs() << "}\n";
}

void ExecutionState::addArgContent(llvm::Value *val) {
  argContents.insert(val);
}

bool ExecutionState::isArgContent(llvm::Value *val) {
  return argContents.find(val) != argContents.end();
}

void ExecutionState::addWrite(std::string newWrite) {
  writeSet.insert(newWrite);
}

std::string ExecutionState::getNextRegNameAndIncrement() {
  std::string value = std::to_string(nextRegName);
  nextRegName++;
  return value;
}

bool ExecutionState::isFunctionForAnalysis(llvm::Function *func) {
  std::vector<std::string> removedFunctions = {"__uClibc_main", "__uClibc_init", "__uClibc_fini", "__user_main",
    "exit", "map_allocate", "map_lookup_elem", "map_update_elem", "map_delete_elem", 
    "map_of_map_allocate", "map_of_map_lookup_elem", "bpf_map_init_stub", "bpf_xdp_adjust_head",
    "bpf_map_lookup_elem", "bpf_map_reset_stub", "array_allocate", "bpf_map_update_elem",
    "array_update_elem", "bpf_redirect_map", "map_update_elem", "array_lookup_elem", ""};
  std::string funcName = func->getName().str();

  // not present in the removed functions
  return std::find(removedFunctions.begin(), removedFunctions.end(), funcName) == removedFunctions.end();
}

bool ExecutionState::isAddressValue(llvm::Value *val) {
  // DANATODO: This is very crude, and only a temp fix that still has bugs
  // It could happen that there is a member of a struct named addr
  std::string valName = val->getName().str();
  std::string addressVars = ".addr";

  return valName.find(addressVars) != std::string::npos;
}

bool ExecutionState::isValueForAnalysis(llvm::Value *val) {
  std::vector<std::string> removedNames{"", "retval", "argc.addr", "argv.addr"};
  std::string valName = val->getName().str();
  std::string addressVars = ".addr";

  const std::regex tempVarRegex("((.)+\\.[0-9]+)");

  if (valName.find("retval") != std::string::npos) {
    return false;
  }

  if (std::regex_match(valName, tempVarRegex)) {
    llvm::errs() << "Regex matched on " << valName << "\n";
    return false;
  }

  return std::find(removedNames.begin(), removedNames.end(), valName) == removedNames.end();
}

void ExecutionState::setPacketBaseAddr(ref<Expr> base) {
  packetBaseAddr = base;
}

ref<Expr> ExecutionState::getPacketBaseAddr() {
  return packetBaseAddr;
}

void ExecutionState::setPacketEndAddr(ref<Expr> end) {
  packetEndAddr = end;
}

ref<Expr> ExecutionState::getPacketEndAddr() {
  return packetEndAddr;
}

void ExecutionState::setXDPMemoryObjectID(unsigned int id) {
  xdpMoId = id;
}

unsigned int ExecutionState::getXDPMemoryObjectID() {
  return xdpMoId;
}

bool ExecutionState::isReferencetoMapReturn(llvm::Value *val) {
  for (const auto &c : referencesToMapReturn) {
    if (c.second.find(val) != c.second.end()) {
      return true;
    }
  }
  return false;
}

std::vector<llvm::CallBase*> ExecutionState::findReferenceToMapReturn(llvm::Value *val) {
  std::vector<llvm::CallBase*> mapReturns;
  for (const auto &c : referencesToMapReturn) {
    if (c.second.find(val) != c.second.end()) {
      mapReturns.push_back(c.first);
    }
  }
  return mapReturns;
}

void ExecutionState::createNewMapReturn(llvm::CallBase *val) {
  std::unordered_set<const llvm::Value*> newSet;
  newSet.insert(val);
  referencesToMapReturn.insert(std::make_pair(val, newSet));
  llvm::errs() << "Created new entry for instruction ";
  val->dump();
}

void ExecutionState::addMapString(llvm::Value *val, std::string fName, std::string mapName, const InstructionInfo *info) {
  std::string mapStr = fName + " on map " + mapName + " on line: " + std::to_string(info->line) + ", column: " + std::to_string(info->column);
  mapCallStrings.insert(std::make_pair(val, mapStr));
}

void ExecutionState::printReferencesToMapReturnKeys() {
  llvm::errs() << "References to map return keys: {";
  for (auto &c : referencesToMapReturn) {
    c.first->dump();
  }
  llvm::errs() << "}\n";
}

bool ExecutionState::addIfReferencetoMapReturn(llvm::Value *op, llvm::Value *val) {
  bool added = false;
  for (auto &c : referencesToMapReturn) {
    if (c.second.find(op) != c.second.end() || op == c.first) {
      c.second.insert(val);
      added = true;
    }
  }
  return added;
}

void ExecutionState::removeMapReference(llvm::Value *val) {
  for (auto &c : referencesToMapReturn) {
    c.second.erase(val);
  }
}

void ExecutionState::addMapCorrelation(std::string sourceMap, std::string dependentMap, 
  // add a map correlation between source map and head map
  std::string sourceFunction, std::string dependentFunction) {
  MapCorrelationInformation newInfo;
  newInfo.sourceMapFunction = sourceFunction;
  newInfo.dependentMapFunction = dependentFunction;
  newInfo.sourceMapName = sourceMap;
  newInfo.dependentMapName = dependentMap;
  correlatedMaps.push_back(newInfo);
}

std::vector<std::string> ExecutionState::formatMapCorrelations() {
  std::vector<std::string> mapInfo;

  for (auto &c : correlatedMaps) {
    std::string newInfo = c.sourceMapFunction + "(" + c.sourceMapName + ")->" + c.sourceMapFunction + "(" + c.dependentMapName + ")";
    mapInfo.push_back(newInfo);
  }

  return mapInfo;
}

void ExecutionState::addNewMapLookup(llvm::Value *val, std::string repr) {
  mapLookupString.insert(std::make_pair(val, repr));  
  std::unordered_set<const llvm::Value*> newSet;
  newSet.insert(val);
  mapLookupReturns.insert(std::make_pair(val, newSet));
  llvm::errs() << "Lookup: Created new entry for instruction ";
  val->dump();
}

bool ExecutionState::addIfMapLookupRef(llvm::Value *op, llvm::Value *val) {
  // mapLookupReturns.insert(val);
  bool added = false;
  for (auto &c : mapLookupReturns) {
    if (c.second.find(op) != c.second.end() || op == c.first) {
      c.second.insert(val);
      added = true;
    }
  }
  return added;
}

std::pair<bool, std::string> ExecutionState::isMapLookupReturn(llvm::Value *val) {
  for (const auto &c : mapLookupReturns) {
    if (c.second.find(val) != c.second.end()) {
      return std::make_pair(true, mapLookupString[c.first]);
    }
  }
  return std::make_pair(false, "");
}

void ExecutionState::addBranchOnMapReturn(llvm::Value *val, const InstructionInfo *info) {
  std::string branchInfo = "line: " + std::to_string(info->line) + ", column: " + std::to_string(info->column);
  branchesOnMapReturnReference.insert(std::make_pair(val, branchInfo));
}

std::string ExecutionState::formatBranchMaps() {
  std::string maps;

  for (auto &branch : branchesOnMapReturnReference) {
    for (auto &c: findReferenceToMapReturn(branch.first)) {
      llvm::errs() << "Reference to ";
      c->dump();
      std::string mapStr = "Unknown map and function\n";
      auto it = mapCallStrings.find(c);
      if (it != mapCallStrings.end()) {
        mapStr = "\tBranch on " + branch.second + " used return value from call to " + it->second + "\n";
      }
      maps += mapStr;
    }
  }

  return maps;
}

void ExecutionState::pushFrame(KInstIterator caller, KFunction *kf) {
  stack.emplace_back(StackFrame(caller, kf));
}

void ExecutionState::popFrame() {
  const StackFrame &sf = stack.back();
  for (const auto *memoryObject : sf.allocas) {
    deallocate(memoryObject);
    addressSpace.unbindObject(memoryObject);
  }
  stack.pop_back();
}

void ExecutionState::deallocate(const MemoryObject *mo) {
  if (SingleObjectResolution) {
    auto mos_it = base_mos.find(mo->address);
    if (mos_it != base_mos.end()) {
      for (auto it = mos_it->second.begin(); it != mos_it->second.end(); ++it) {
        base_addrs.erase(*it);
      }
      base_mos.erase(mos_it->first);
    }
  }

  if (!stackAllocator || !heapAllocator)
    return;

  auto address = reinterpret_cast<void *>(mo->address);
  if (mo->isLocal) {
    stackAllocator.free(address, std::max(mo->size, mo->alignment));
  } else {
    heapAllocator.free(address, std::max(mo->size, mo->alignment));
  }
}

void ExecutionState::addSymbolic(const MemoryObject *mo, const Array *array) {
  symbolics.emplace_back(ref<const MemoryObject>(mo), array);
}

/**/

llvm::raw_ostream &klee::operator<<(llvm::raw_ostream &os, const MemoryMap &mm) {
  os << "{";
  MemoryMap::iterator it = mm.begin();
  MemoryMap::iterator ie = mm.end();
  if (it!=ie) {
    os << "MO" << it->first->id << ":" << it->second.get();
    for (++it; it!=ie; ++it)
      os << ", MO" << it->first->id << ":" << it->second.get();
  }
  os << "}";
  return os;
}

bool ExecutionState::merge(const ExecutionState &b) {
  if (DebugLogStateMerge)
    llvm::errs() << "-- attempting merge of A:" << this << " with B:" << &b
                 << "--\n";
  if (pc != b.pc)
    return false;

  // XXX is it even possible for these to differ? does it matter? probably
  // implies difference in object states?

  if (symbolics != b.symbolics)
    return false;

  {
    std::vector<StackFrame>::const_iterator itA = stack.begin();
    std::vector<StackFrame>::const_iterator itB = b.stack.begin();
    while (itA!=stack.end() && itB!=b.stack.end()) {
      // XXX vaargs?
      if (itA->caller!=itB->caller || itA->kf!=itB->kf)
        return false;
      ++itA;
      ++itB;
    }
    if (itA!=stack.end() || itB!=b.stack.end())
      return false;
  }

  std::set< ref<Expr> > aConstraints(constraints.begin(), constraints.end());
  std::set< ref<Expr> > bConstraints(b.constraints.begin(), 
                                     b.constraints.end());
  std::set< ref<Expr> > commonConstraints, aSuffix, bSuffix;
  std::set_intersection(aConstraints.begin(), aConstraints.end(),
                        bConstraints.begin(), bConstraints.end(),
                        std::inserter(commonConstraints, commonConstraints.begin()));
  std::set_difference(aConstraints.begin(), aConstraints.end(),
                      commonConstraints.begin(), commonConstraints.end(),
                      std::inserter(aSuffix, aSuffix.end()));
  std::set_difference(bConstraints.begin(), bConstraints.end(),
                      commonConstraints.begin(), commonConstraints.end(),
                      std::inserter(bSuffix, bSuffix.end()));
  if (DebugLogStateMerge) {
    llvm::errs() << "\tconstraint prefix: [";
    for (std::set<ref<Expr> >::iterator it = commonConstraints.begin(),
                                        ie = commonConstraints.end();
         it != ie; ++it)
      llvm::errs() << *it << ", ";
    llvm::errs() << "]\n";
    llvm::errs() << "\tA suffix: [";
    for (std::set<ref<Expr> >::iterator it = aSuffix.begin(),
                                        ie = aSuffix.end();
         it != ie; ++it)
      llvm::errs() << *it << ", ";
    llvm::errs() << "]\n";
    llvm::errs() << "\tB suffix: [";
    for (std::set<ref<Expr> >::iterator it = bSuffix.begin(),
                                        ie = bSuffix.end();
         it != ie; ++it)
      llvm::errs() << *it << ", ";
    llvm::errs() << "]\n";
  }

  // We cannot merge if addresses would resolve differently in the
  // states. This means:
  // 
  // 1. Any objects created since the branch in either object must
  // have been free'd.
  //
  // 2. We cannot have free'd any pre-existing object in one state
  // and not the other

  if (DebugLogStateMerge) {
    llvm::errs() << "\tchecking object states\n";
    llvm::errs() << "A: " << addressSpace.objects << "\n";
    llvm::errs() << "B: " << b.addressSpace.objects << "\n";
  }
    
  std::set<const MemoryObject*> mutated;
  MemoryMap::iterator ai = addressSpace.objects.begin();
  MemoryMap::iterator bi = b.addressSpace.objects.begin();
  MemoryMap::iterator ae = addressSpace.objects.end();
  MemoryMap::iterator be = b.addressSpace.objects.end();
  for (; ai!=ae && bi!=be; ++ai, ++bi) {
    if (ai->first != bi->first) {
      if (DebugLogStateMerge) {
        if (ai->first < bi->first) {
          llvm::errs() << "\t\tB misses binding for: " << ai->first->id << "\n";
        } else {
          llvm::errs() << "\t\tA misses binding for: " << bi->first->id << "\n";
        }
      }
      return false;
    }
    if (ai->second.get() != bi->second.get()) {
      if (DebugLogStateMerge)
        llvm::errs() << "\t\tmutated: " << ai->first->id << "\n";
      mutated.insert(ai->first);
    }
  }
  if (ai!=ae || bi!=be) {
    if (DebugLogStateMerge)
      llvm::errs() << "\t\tmappings differ\n";
    return false;
  }
  
  // merge stack

  ref<Expr> inA = ConstantExpr::alloc(1, Expr::Bool);
  ref<Expr> inB = ConstantExpr::alloc(1, Expr::Bool);
  for (std::set< ref<Expr> >::iterator it = aSuffix.begin(), 
         ie = aSuffix.end(); it != ie; ++it)
    inA = AndExpr::create(inA, *it);
  for (std::set< ref<Expr> >::iterator it = bSuffix.begin(), 
         ie = bSuffix.end(); it != ie; ++it)
    inB = AndExpr::create(inB, *it);

  // XXX should we have a preference as to which predicate to use?
  // it seems like it can make a difference, even though logically
  // they must contradict each other and so inA => !inB

  std::vector<StackFrame>::iterator itA = stack.begin();
  std::vector<StackFrame>::const_iterator itB = b.stack.begin();
  for (; itA!=stack.end(); ++itA, ++itB) {
    StackFrame &af = *itA;
    const StackFrame &bf = *itB;
    for (unsigned i=0; i<af.kf->numRegisters; i++) {
      ref<Expr> &av = af.locals[i].value;
      const ref<Expr> &bv = bf.locals[i].value;
      if (!av || !bv) {
        // if one is null then by implication (we are at same pc)
        // we cannot reuse this local, so just ignore
      } else {
        av = SelectExpr::create(inA, av, bv);
      }
    }
  }

  for (std::set<const MemoryObject*>::iterator it = mutated.begin(), 
         ie = mutated.end(); it != ie; ++it) {
    const MemoryObject *mo = *it;
    const ObjectState *os = addressSpace.findObject(mo);
    const ObjectState *otherOS = b.addressSpace.findObject(mo);
    assert(os && !os->readOnly && 
           "objects mutated but not writable in merging state");
    assert(otherOS);

    ObjectState *wos = addressSpace.getWriteable(mo, os);
    for (unsigned i=0; i<mo->size; i++) {
      ref<Expr> av = wos->read8(i);
      ref<Expr> bv = otherOS->read8(i);
      wos->write(i, SelectExpr::create(inA, av, bv));
    }
  }

  constraints = ConstraintSet();

  ConstraintManager m(constraints);
  for (const auto &constraint : commonConstraints)
    m.addConstraint(constraint);
  m.addConstraint(OrExpr::create(inA, inB));

  return true;
}

void ExecutionState::dumpStack(llvm::raw_ostream &out) const {
  unsigned idx = 0;
  const KInstruction *target = prevPC;
  for (ExecutionState::stack_ty::const_reverse_iterator
         it = stack.rbegin(), ie = stack.rend();
       it != ie; ++it) {
    const StackFrame &sf = *it;
    Function *f = sf.kf->function;
    const InstructionInfo &ii = *target->info;
    out << "\t#" << idx++;
    std::stringstream AssStream;
    AssStream << std::setw(8) << std::setfill('0') << ii.assemblyLine;
    out << AssStream.str();
    out << " in " << f->getName().str() << "(";
    // Yawn, we could go up and print varargs if we wanted to.
    unsigned index = 0;
    for (Function::arg_iterator ai = f->arg_begin(), ae = f->arg_end();
         ai != ae; ++ai) {
      if (ai!=f->arg_begin()) out << ", ";

      if (ai->hasName())
        out << ai->getName().str() << "=";

      ref<Expr> value = sf.locals[sf.kf->getArgRegister(index++)].value;
      if (isa_and_nonnull<ConstantExpr>(value)) {
        out << value;
      } else {
        out << "symbolic";
      }
    }
    out << ")";
    if (ii.file != "")
      out << " at " << ii.file << ":" << ii.line;
    out << "\n";
    target = sf.caller;
  }
}

void ExecutionState::addConstraint(ref<Expr> e) {
  ConstraintManager c(constraints);
  c.addConstraint(e);
}

void ExecutionState::addCexPreference(const ref<Expr> &cond) {
  cexPreferences = cexPreferences.insert(cond);
}
