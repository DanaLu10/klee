//===-- ExecutionState.h ----------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_EXECUTIONSTATE_H
#define KLEE_EXECUTIONSTATE_H

#include "AddressSpace.h"
#include "MemoryManager.h"
#include "MergeHandler.h"

#include "klee/ADT/ImmutableSet.h"
#include "klee/ADT/TreeStream.h"
#include "klee/Expr/Constraints.h"
#include "klee/Expr/Expr.h"
#include "klee/KDAlloc/kdalloc.h"
#include "klee/Module/KInstIterator.h"
#include "klee/Solver/Solver.h"
#include "klee/System/Time.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include <unordered_set>

#include <map>
#include <memory>
#include <set>
#include <vector>

namespace klee {
class Array;
class CallPathNode;
struct Cell;
class ExecutionTreeNode;
struct KFunction;
struct KInstruction;
class MemoryObject;
struct InstructionInfo;

llvm::raw_ostream &operator<<(llvm::raw_ostream &os, const MemoryMap &mm);

struct StackFrame {
  KInstIterator caller;
  KFunction *kf;
  CallPathNode *callPathNode;

  std::vector<const MemoryObject *> allocas;
  Cell *locals;

  /// Minimum distance to an uncovered instruction once the function
  /// returns. This is not a good place for this but is used to
  /// quickly compute the context sensitive minimum distance to an
  /// uncovered instruction. This value is updated by the StatsTracker
  /// periodically.
  unsigned minDistToUncoveredOnReturn;

  // For vararg functions: arguments not passed via parameter are
  // stored (packed tightly) in a local (alloca) memory object. This
  // is set up to match the way the front-end generates vaarg code (it
  // does not pass vaarg through as expected). VACopy is lowered inside
  // of intrinsic lowering.
  MemoryObject *varargs;

  StackFrame(KInstIterator caller, KFunction *kf);
  StackFrame(const StackFrame &s);
  ~StackFrame();
};

/// Contains information related to unwinding (Itanium ABI/2-Phase unwinding)
class UnwindingInformation {
public:
  enum class Kind {
    SearchPhase, // first phase
    CleanupPhase // second phase
  };

private:
  const Kind kind;

public:
  // _Unwind_Exception* of the thrown exception, used in both phases
  ref<ConstantExpr> exceptionObject;

  Kind getKind() const { return kind; }

  explicit UnwindingInformation(ref<ConstantExpr> exceptionObject, Kind k)
      : kind(k), exceptionObject(exceptionObject) {}
  virtual ~UnwindingInformation() = default;

  virtual std::unique_ptr<UnwindingInformation> clone() const = 0;
};

struct SearchPhaseUnwindingInformation : public UnwindingInformation {
  // Keeps track of the stack index we have so far unwound to.
  std::size_t unwindingProgress;

  // MemoryObject that contains a serialized version of the last executed
  // landingpad, so we can clean it up after the personality fn returns.
  MemoryObject *serializedLandingpad = nullptr;

  SearchPhaseUnwindingInformation(ref<ConstantExpr> exceptionObject,
                                  std::size_t const unwindingProgress)
      : UnwindingInformation(exceptionObject,
                             UnwindingInformation::Kind::SearchPhase),
        unwindingProgress(unwindingProgress) {}

  std::unique_ptr<UnwindingInformation> clone() const {
    return std::make_unique<SearchPhaseUnwindingInformation>(*this);
  }

  static bool classof(const UnwindingInformation *u) {
    return u->getKind() == UnwindingInformation::Kind::SearchPhase;
  }
};

struct CleanupPhaseUnwindingInformation : public UnwindingInformation {
  // Phase 1 will try to find a catching landingpad.
  // Phase 2 will unwind up to this landingpad or return from
  // _Unwind_RaiseException if none was found.

  // The selector value of the catching landingpad that was found
  // during the search phase.
  ref<ConstantExpr> selectorValue;

  // Used to know when we have to stop unwinding and to
  // ensure that unwinding stops at the frame for which
  // we first found a handler in the search phase.
  const std::size_t catchingStackIndex;

  CleanupPhaseUnwindingInformation(ref<ConstantExpr> exceptionObject,
                                   ref<ConstantExpr> selectorValue,
                                   const std::size_t catchingStackIndex)
      : UnwindingInformation(exceptionObject,
                             UnwindingInformation::Kind::CleanupPhase),
        selectorValue(selectorValue),
        catchingStackIndex(catchingStackIndex) {}

  std::unique_ptr<UnwindingInformation> clone() const {
    return std::make_unique<CleanupPhaseUnwindingInformation>(*this);
  }

  static bool classof(const UnwindingInformation *u) {
    return u->getKind() == UnwindingInformation::Kind::CleanupPhase;
  }
};

enum class MapType {
  Array,
  Map,
  MapOfMap
};

struct MapInfo {
  std::string mapName;
  unsigned int mapSize;
  unsigned int keySize;
  unsigned int valueSize;
  MapType mapType;
};

struct BranchInfo {
  llvm::Value* branch;
  unsigned int sourceLine;
  unsigned int sourceColumn;
  std::string sourceFile;
  ref<Expr> cond;

  bool operator<(const BranchInfo& y) const {
    return std::tie(sourceLine, sourceColumn) < std::tie(y.sourceLine, y.sourceColumn);
  }
};

// bool operator<(const BranchInfo& x, const BranchInfo& y);

struct CallInfo {
  unsigned int sourceLine;
  unsigned int sourceColumn;
  std::string sourceFile;
  std::string functionName;
  std::string mapName;
  std::string key;
  std::string value;
  std::unordered_set<const llvm::Value*> references;
};

/// @brief ExecutionState representing a path under exploration
class ExecutionState {
#ifdef KLEE_UNITTEST
public:
#else
private:
#endif
  // copy ctor
  ExecutionState(const ExecutionState &state);

public:
  using stack_ty = std::vector<StackFrame>;

  // Execution - Control Flow specific

  /// @brief Pointer to instruction to be executed after the current
  /// instruction
  KInstIterator pc;

  /// @brief Pointer to instruction which is currently executed
  KInstIterator prevPC;

  /// @brief Stack representing the current instruction stream
  stack_ty stack;

  /// @brief Remember from which Basic Block control flow arrived
  /// (i.e. to select the right phi values)
  std::uint32_t incomingBBIndex;

  // Overall state of the state - Data specific

  /// @brief Exploration depth, i.e., number of times KLEE branched for this state
  std::uint32_t depth = 0;

  /// @brief Address space used by this state (e.g. Global and Heap)
  AddressSpace addressSpace;

  /// @brief Stack allocator (used with deterministic allocation)
  kdalloc::StackAllocator stackAllocator;

  /// @brief Heap allocator (used with deterministic allocation)
  kdalloc::Allocator heapAllocator;

  /// @brief Constraints collected so far
  ConstraintSet constraints;

  /// Statistics and information

  /// @brief Metadata utilized and collected by solvers for this state
  mutable SolverQueryMetaData queryMetaData;

  /// @brief History of complete path: represents branches taken to
  /// reach/create this state (both concrete and symbolic)
  TreeOStream pathOS;

  /// @brief History of symbolic path: represents symbolic branches
  /// taken to reach/create this state
  TreeOStream symPathOS;

  /// @brief Set containing which lines in which files are covered by this state
  std::map<const std::string *, std::set<std::uint32_t>> coveredLines;

  /// @brief Pointer to the execution tree of the current state
  /// Copies of ExecutionState should not copy executionTreeNode
  ExecutionTreeNode *executionTreeNode = nullptr;

  /// @brief Ordered list of symbolics: used to generate test cases.
  //
  // FIXME: Move to a shared list structure (not critical).
  std::vector<std::pair<ref<const MemoryObject>, const Array *>> symbolics;

  /// @brief A set of boolean expressions
  /// the user has requested be true of a counterexample.
  ImmutableSet<ref<Expr>> cexPreferences;

  /// @brief Set of used array names for this state.  Used to avoid collisions.
  std::set<std::string> arrayNames;

  /// @brief The objects handling the klee_open_merge calls this state ran through
  std::vector<ref<MergeHandler>> openMergeStack;

  /// @brief The numbers of times this state has run through Executor::stepInstruction
  std::uint64_t steppedInstructions = 0;

  /// @brief Counts how many instructions were executed since the last new
  /// instruction was covered.
  std::uint32_t instsSinceCovNew = 0;

  /// @brief Keep track of unwinding state while unwinding, otherwise empty
  std::unique_ptr<UnwindingInformation> unwindingInformation;

  /// @brief the global state counter
  static std::uint32_t nextID;

  /// @brief the state id
  std::uint32_t id = 0;

  /// @brief Whether a new instruction was covered in this state
  bool coveredNew = false;

  /// @brief Disables forking for this state. Set by user code
  bool forkDisabled = false;

  /// @brief Mapping symbolic address expressions to concrete base addresses
  using base_addrs_t = std::map<ref<Expr>, ref<ConstantExpr>>;
  base_addrs_t base_addrs;
  /// @brief Mapping MemoryObject addresses to refs used in the base_addrs map
  using base_mo_t = std::map<uint64_t, std::set<ref<Expr>>>;
  base_mo_t base_mos;

  /// @brief Packet read set of path.
  std::set<std::string> packetRead;

  /// @brief Packet write of path.
  std::set<std::string> packetWrite;

  /// @brief Map read set of path.
  std::unordered_map<std::string, std::set<std::pair<ref<Expr>, std::string>>> mapRead;

  /// @brief Map write set of path.
  std::unordered_map<std::string, std::set<std::pair<ref<Expr>, std::string>>> mapWrite;

  /// @brief Set of values which are part of the references to the arguments of a function
  std::unordered_set<llvm::Value*> argContents;

  /// @brief Mapping from lookup call to string representation of map name with key value
  std::unordered_map<llvm::Value*, std::string> mapLookupString;

  /// @brief Set of values which are references to a location returned by a lookup
  std::unordered_map<llvm::Value*, std::unordered_set<const llvm::Value*>> mapLookupReturns;

  /// @brief Mapping from map helper function call to information on that call
  std::unordered_map<llvm::Value*, CallInfo> callInformation;
  
  /// @brief Map from the memory object ID of that map to the name of the map and size of the key
  std::unordered_map<unsigned int, MapInfo> mapMemoryObjects;

  /// @brief Mapping from calls to map helper functions to a string representation and call key
  std::unordered_map<llvm::Value*, std::pair<std::string, std::string>> mapCallStrings;
  std::unordered_map<llvm::Value*, ref<Expr>> mapCallArgumentExpressions;

  /// @brief Set of calls to map helper functions which result in a branch
  std::set<BranchInfo> branchesOnMapReturnReference;

  /// @brief Set of map pairs where there is a correlation from the left map to the right map
  std::set<std::pair<std::pair<llvm::Value*, llvm::Value*>, std::string>> correlatedMaps;

  unsigned int xdpMoId = 0;

  std::string nextMapName;
  std::string nextMapKey;
  unsigned int nextMapSize;
  unsigned int nextKeySize;
  unsigned int nextValueSize;
  ref<Expr> mapOperationKey;

  bool generateMode = true;

  std::set<std::string> overlap;

public:
#ifdef KLEE_UNITTEST
  // provide this function only in the context of unittests
  ExecutionState() = default;
#endif
  // only to create the initial state
  explicit ExecutionState(KFunction *kf, MemoryManager *mm);
  // no copy assignment, use copy constructor
  ExecutionState &operator=(const ExecutionState &) = delete;
  // no move ctor
  ExecutionState(ExecutionState &&) noexcept = delete;
  // no move assignment
  ExecutionState& operator=(ExecutionState &&) noexcept = delete;
  // dtor
  ~ExecutionState();

  ExecutionState *branch();

  void addPacketRead(std::string newRead);
  void addMapRead(std::string mapName, ref<Expr> key, std::string keyName);
  // void addRead(std::string mapName, std::string keyValue, unsigned int keySize);
  void addPacketWrite(std::string newWrite);
  void addMapWrite(std::string mapName, ref<Expr> key, std::string keyName);
  // void addWrite(std::string mapName, std::string keyValue, unsigned int keySize);
  std::set<std::pair<ref<Expr>, std::string>> getMapRead(std::string mapName);
  std::set<std::pair<ref<Expr>, std::string>> getMapWrite(std::string mapName);
  ref<Expr> getMapReadForString(std::string mapName, std::string keyName);
  void addToOverlap(std::string mapName, std::string keyValue);

  std::set<std::string> getReadSet();
  std::set<std::string> getWriteSet();

  bool isFunctionForAnalysis(llvm::Function *func);
  bool isAddressValue(llvm::Value *val);

  void setXDPMemoryObjectID(unsigned int id);
  unsigned int getXDPMemoryObjectID();

  bool isReferencetoMapReturn(llvm::Value *val);
  void createNewMapReturn(llvm::Value *val, const InstructionInfo *kiInfo, 
    std::string functionName, std::string mapName, std::string keyVal, std::string value);
  // If op is in any of the sets of values that reference a return value of a map helper
  // function call, add val into those sets
  bool addIfReferencetoMapReturn(llvm::Value *op, llvm::Value *val);
  void removeMapReference(llvm::Value *val);

  bool addIfMapLookupRef(llvm::Value *op, llvm::Value *val);
  void addNewMapLookup(llvm::Value *val, std::string repr);
  std::pair<bool, std::string> isMapLookupReturn(llvm::Value *val);

  void addMapString(llvm::Value *val, std::string fName, std::string mapName, std::string key, const InstructionInfo *info, ref<Expr> keyExpr);
  std::string getMapCallKey(llvm::Value *val);
  ref<Expr> getMapCallExpr(llvm::Value *val);

  void addBranchOnMapReturn(llvm::Value *val, const InstructionInfo *info, ref<Expr> cond);
  std::string formatBranchMaps();
  std::vector<llvm::Value*> findOriginalMapCall(llvm::Value *val);

  void addMapCorrelation(llvm::Value *sourceCall, llvm::Value *destCall, std::string arg);
  std::set<std::string> formatMapCorrelations();
  void printReferencesToMapReturnKeys();

  void addMapMemoryObjects(unsigned int id, std::string allocateFunctionName);

  MapInfo getMapInfo(unsigned int id);
  bool isMapMemoryObject(unsigned int id);
  void printMapMemoryObjects();

  void pushFrame(KInstIterator caller, KFunction *kf);
  void popFrame();

  void deallocate(const MemoryObject *mo);

  void addSymbolic(const MemoryObject *mo, const Array *array);

  void addConstraint(ref<Expr> e);
  void addCexPreference(const ref<Expr> &cond);

  bool merge(const ExecutionState &b);
  void dumpStack(llvm::raw_ostream &out) const;

  std::uint32_t getID() const { return id; };
  void setID() { id = nextID++; };
  static std::uint32_t getLastID() { return nextID - 1; };
};

struct ExecutionStateIDCompare {
  bool operator()(const ExecutionState *a, const ExecutionState *b) const {
    return a->getID() < b->getID();
  }
};
}

#endif /* KLEE_EXECUTIONSTATE_H */
