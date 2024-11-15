-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [test]
import Base
open Primitives
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

namespace test

/- [test::MyStruct]
   Source: 'test.rs', lines 7:1-7:16 -/
structure MyStruct where
  a : I32
  b : Bool

/- [test::struct_project]:
   Source: 'test.rs', lines 12:1-12:38 -/
def struct_project (s : MyStruct) : Result I32 :=
  Result.ok s.a

/- [test::main]:
   Source: 'test.rs', lines 17:1-17:10 -/
def main : Result Unit :=
  do
  let _ ← struct_project { a := 1#i32, b := true }
  Result.ok ()

end test
