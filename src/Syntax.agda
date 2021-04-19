module Syntax where

open import Data.List renaming (and to and' ; drop to drop' ; align to algin')
open import Types
open import Data.Bool renaming (not to not')
open import Data.Nat renaming (ℕ to Nat)
open import Data.Maybe renaming (align to align')
open import Data.Integer renaming (ℤ to Int)
open import Data.Word
open import Data.String hiding (_==_)
record U64 : Set where
  constructor u64
  field
    raw : Word64

record U32 : Set where
  constructor u32
  field
    raw : Word64
    limit : toℕ raw Data.Nat.≤ 0xffffffff

record U16 : Set where
  constructor u16
  field
    raw : Word64
    limit : toℕ raw Data.Nat.≤ 0xffff

record Byte : Set where
  constructor u8
  field
    raw : Word64
    limit : toℕ raw Data.Nat.≤ 0xff

record limits : Set where
  field
    min : U64
    max : Maybe U64

memtype = limits

data valtype : Set where
  i32 : valtype
  i64 : valtype

resulttype = List valtype
functype = arrow resulttype resulttype

data val : Set where -- raw value expressions
  i32 : U32 → val
  i64 : U64 → val

record memarg : Set where
  field
    offset : Nat
    align : Nat

data insn : Set where
  -- numerical instructions
  const : val → insn
  not : insn
  and : insn
  add : insn
  sub : insn
  eqz : insn
  dup : insn
  drop : insn

  -- memory instructions
  memory-size : insn
  memory-grow : insn
  memory-fill : insn
  memory-copy : insn
  memory-init : insn
  load : valtype → memarg → insn
  store : valtype → memarg → insn
  load8 : valtype → memarg → insn
  store8 : valtype → memarg → insn
  load16 : valtype → memarg → insn
  store16 : valtype → memarg → insn

  -- control instructions
  nop : insn
  block : functype → List insn → insn
  if-else : functype → List insn → List insn → insn
  loop : functype → List insn → insn
  br : U64 → insn

vals : Set
vals = List val

insns : Set
insns = List insn

record mem : Set where
  field
    type : memtype
    dat : U32 → Byte

data blockctx : Set where
  ∙ : blockctx
  _[_]_ : vals → blockctx → insns → blockctx

record configuration : Set where
  constructor
    config
  field
    st : mem
    vs : vals
    is : insns
    bctx : blockctx