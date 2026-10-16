/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module

prelude
public import Lean.Expr

public section

namespace Lean

/--
Datastructure for representing the "head symbol" of an expression.
It is the key of `KExprMap`.
Examples:
- The head of `f a` is `.const f`
- The head of `let x := 1; f x` is `.const f`
- The head of `fun x => fun` is `.lam`

`HeadIndex` is a very simple index, and is used in situations where
we want to find definitionally equal terms, but we want to minimize
the search by checking only pairs of terms that have the same
`HeadIndex`.
-/
inductive HeadIndex where
  | fvar (fvarId : FVarId)
  | mvar (mvarId : MVarId)
  | const (constName : Name)
  | proj (structName : Name) (idx : Nat)
  | lit (litVal : Literal)
  | sort
  | lam
  | forallE
  deriving Inhabited, BEq, Repr

/-- Hash code for a `HeadIndex` value. -/
protected def HeadIndex.hash : HeadIndex → UInt64
  | fvar fvarId         => mixHash 11 <| hash fvarId
  | mvar mvarId         => mixHash 13 <| hash mvarId
  | const constName     => mixHash 17 <| hash constName
  | proj structName idx => mixHash 19 <| mixHash (hash structName) (hash idx)
  | lit litVal          => mixHash 23 <| hash litVal
  | sort                => 29
  | lam                 => 31
  | forallE             => 37

instance : Hashable HeadIndex := ⟨HeadIndex.hash⟩

namespace Expr

/-- Return the number of arguments in the given expression with respect to its `HeadIndex` -/
def headNumArgs (e : Expr) : Nat :=
  go e 0
where
  go : Expr → Nat → Nat
  | app f _, n        => go f (n + 1)
  | letE _ _ _ b _, n => go b n
  | mdata _ e, n      => go e n
  | _, n              => n

/--
  Quick version that may fail if it "hits" a loose bound variable.
  This can happen, for example, if the input expression is of the form.
  ```
  let f := fun x => x + 1;
  f 0
  ```
-/
private def toHeadIndexQuick? : Expr → Option HeadIndex
  | mvar mvarId             => HeadIndex.mvar mvarId
  | fvar fvarId             => HeadIndex.fvar fvarId
  | const constName _       => HeadIndex.const constName
  | proj structName idx _   => HeadIndex.proj structName idx
  | sort _                  => HeadIndex.sort
  | lam ..                  => HeadIndex.lam
  | forallE ..              => HeadIndex.forallE
  | lit v                   => HeadIndex.lit v
  | app f _                 => toHeadIndexQuick? f
  | letE _ _ _ b _          => toHeadIndexQuick? b
  | mdata _ e               => toHeadIndexQuick? e
  | _                       => none

/--
  Slower version of `toHeadIndexQuick?` that "expands" let-declarations to make
  sure we never hit a loose bound variable.
  The performance of the `letE` alternative can be improved, but this function should not be in the hotpath
  since `toHeadIndexQuick?` succeeds most of the time.
-/
private partial def toHeadIndexSlow : Expr → HeadIndex
  | mvar mvarId             => HeadIndex.mvar mvarId
  | fvar fvarId             => HeadIndex.fvar fvarId
  | const constName _       => HeadIndex.const constName
  | proj structName idx _   => HeadIndex.proj structName idx
  | sort _                  => HeadIndex.sort
  | lam ..                  => HeadIndex.lam
  | forallE ..              => HeadIndex.forallE
  | lit v                   => HeadIndex.lit v
  | app f _                 => toHeadIndexSlow f
  | letE _ _ v b _          => toHeadIndexSlow (b.instantiate1 v)
  | mdata _ e               => toHeadIndexSlow e
  | _                       => panic! "unexpected expression kind"

/--
Convert the given expression into a `HeadIndex`.
-/
def toHeadIndex (e : Expr) : HeadIndex :=
  match toHeadIndexQuick? e with
  | some i => i
  | none => toHeadIndexSlow e

/--
Result of comparing the head of an expression with a `HeadIndex` as in `toHeadIndexQuick?`:
`0` if they differ, `1` if they agree, and `2` if the quick version fails.
-/
private def headIndexQuickEq (h : HeadIndex) : Expr → UInt8
  | mvar mvarId             => match h with | .mvar m => if m == mvarId then 1 else 0 | _ => 0
  | fvar fvarId             => match h with | .fvar f => if f == fvarId then 1 else 0 | _ => 0
  | const constName _       => match h with | .const n => if n == constName then 1 else 0 | _ => 0
  | proj structName idx _   =>
    match h with | .proj s i => if s == structName && i == idx then 1 else 0 | _ => 0
  | sort _                  => match h with | .sort => 1 | _ => 0
  | lam ..                  => match h with | .lam => 1 | _ => 0
  | forallE ..              => match h with | .forallE => 1 | _ => 0
  | lit v                   => match h with | .lit l => if l == v then 1 else 0 | _ => 0
  | app f _                 => headIndexQuickEq h f
  | letE _ _ _ b _          => headIndexQuickEq h b
  | mdata _ e               => headIndexQuickEq h e
  | _                       => 2

/--
`e.toHeadIndex == h`, without allocating the `HeadIndex` of `e` when the quick version succeeds.
-/
def hasHeadIndex (e : Expr) (h : HeadIndex) : Bool :=
  match headIndexQuickEq h e with
  | 0 => false
  | 1 => true
  | _ => toHeadIndexSlow e == h

end Expr
end Lean
