// RUN: %clang %s -fsanitize=shift-exponent -emit-llvm -g %O0opt -c -o %t.bc
// RUN: rm -rf %t.klee-out
// RUN: %klee --output-dir=%t.klee-out --emit-all-errors --ubsan-runtime %t.bc 2>&1 | FileCheck %s

#include "klee/klee.h"

int rsh_inbounds(signed int a, signed int b) {
  // CHECK: runtime/Sanitizer/ubsan/ubsan_handlers.cpp:35: shift out of bounds
  return a >> b;
}

int main() {
  signed int a;
  signed int b;
  volatile signed int result;

  klee_make_symbolic(&a, sizeof(a), "a");
  klee_make_symbolic(&b, sizeof(b), "b");

  result = rsh_inbounds(a, b);

  return 0;
}