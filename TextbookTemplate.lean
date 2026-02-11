import Lean
import Lean.Elab.Term
import VersoManual
import TextbookTemplate.Meta.Lean
import TextbookTemplate.Papers

open Lean Elab Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open TextbookTemplate

set_option pp.rawOnError true
set_option quotPrecheck false

#doc (Manual) "Software Foundations in Lean" =>

%%%
authors := ["Steven Holtzen"]
%%%


# Typed arithmetic expressions

Consider the following surface syntax of expressions:

```
t ::= true
    | false
    | if t then t else t
    | 0
    | succ t
    | pred t
    | iszero t
```

This can be encoded as the following Lean inductive type:

```savedLean
/--
  An inductive type of typed arithmetic expressions.
-/
inductive tm : Type where
| fls : tm
| tru : tm
| ite : tm -> tm -> tm -> tm
| zro : tm
| succ : tm -> tm
| prd : tm -> tm
| iszro : tm -> tm
```

Now we can give this language a simple surface syntax for working with it:

```savedLean
declare_syntax_cat tarith
syntax "false" : tarith
syntax "true" : tarith
syntax "[" term "]": tarith
syntax "if" tarith "then" tarith "else" tarith : tarith
syntax:100 "(" tarith ")" : tarith
syntax "zero" : tarith
syntax "pred" tarith : tarith
syntax "succ" tarith : tarith
syntax "zero?" tarith : tarith

partial def tm.elab (t : TSyntax `tarith) : TermElabM Expr :=
  match t with
  | `(tarith| ( $e ) ) => tm.elab e
  | `(tarith| [ $e:term ]) => do
    let expr ← Term.elabTerm e none
    return expr
  | `(tarith| true) => do
    mkAppM ``tm.tru #[]
  | `(tarith| false) => do
    mkAppM ``tm.fls #[]
  | `(tarith| if $e1 then $e2 else $e3 ) => do
   mkAppM ``tm.ite #[<- tm.elab e1,
                     <- tm.elab e2,
                     <- tm.elab e3]
  | `(tarith| zero) => do
    mkAppM ``tm.zro #[]
  | `(tarith| succ $e1) => do
    mkAppM ``tm.succ #[<- tm.elab e1]
  | `(tarith| pred $e1) => do
    mkAppM ``tm.prd #[<- tm.elab e1]
  | `(tarith| zero? $e1) => do
    mkAppM ``tm.iszro #[<- tm.elab e1]
  | _ => throwUnsupportedSyntax

elab "{{" e:tarith "}}" : term => tm.elab e
```

Now we can use our parser and elaborator together to easily parse
typed arithmetic expressions:

```lean (name := parse_tarith)
#eval {{ if (zero? zero) then true else false }}
-- here is an example showcasing the unquote mechanism
#eval {{ if [ tm.zro ] then true else false}}
```
```leanOutput parse_tarith
tm.ite (tm.iszro (tm.zro)) (tm.tru) (tm.fls)
```

## Operational semantics

First let's define a notion of values:

```savedLean
/--
  Boolean values
-/
inductive bvalue : tm -> Prop
| bv_true : bvalue {{true}}
| bv_false : bvalue {{false}}

/--
  Numeric values
-/
inductive nvalue : tm -> Prop
| nv_0 : nvalue {{zero}}
| nv_succ : nvalue t -> nvalue {{succ [t]}}

def value (t : tm) : Prop := bvalue t ∨ nvalue t
```

Let's give operational semantics for this language:

```savedLean
inductive step : tm -> tm -> Prop
| st_if_true : ∀ e1 e2 : tm,
  step {{ if true then [e1] else [e2] }} e1
| st_if_false : ∀ e1 e2 : tm,
  step {{ if false then [e1] else [e2] }} e2
| st_if : ∀ e1 e2 e3 : tm,
  step e1 e1' ->
  step {{ if [e1] then [e2] else [e3] }}
       {{ if [e1'] then [e2] else [e3]}}
| st_succ :
  step e1 e1' ->
  step {{ succ [e1]}} {{ succ [e1']}}
| st_pred0 :
  step {{ pred zero }} {{ zero }}
| st_pred_succ :
  nvalue v ->
  step {{pred (succ [v])}} v
| st_pred :
  step e e' ->
  step {{pred [e]}} {{pred [e']}}
| st_zero?_zero :
  step {{zero? zero}} {{true}}
| st_zero?_succ :
  nvalue v ->
  step {{zero? (succ [v])}} {{false}}
| st_zero? :
  step e e' ->
  step {{zero? [e]}} {{zero? [e']}}
```

## Normal Forms and Values

Sometimes terms can be *stuck*: they cannot take a step and are not a value. For
example:

```savedLean
def relation (X : Type) := X -> X -> Prop

def normal_form (R : relation X) (t : X) : Prop :=
  ¬ ∃ t', R t t'

def step_normal_form := (normal_form step)

def stuck (t : tm) : Prop :=
  step_normal_form t ∧ ¬ value t

```

Let's prove a useful example: there is some stuck term.

```savedLean
example : ∃ t, stuck t := by
  -- the `exists` tactic eliminates the existential
  exists {{if zero then zero else zero}}
  constructor
  · intro ⟨ witness, contradiction ⟩
    cases witness with
    | _ => contradiction
  · intro a
    cases a with
    | _ => contradiction
```

Now let's prove a more interesting theorem: every
value is a normal form.

```savedLean
theorem value_is_nf : ∀ t,
  value t → step_normal_form t := by
  intro tm v
  cases v with
  | inl h =>
    -- boolean value
    intro ⟨ witness, contradiction ⟩
    cases h with
    | _ => contradiction
  | inr h =>
    -- numeric value. We need to do induction here,
    -- in general, it's a good idea to keep your proof
    -- state as simple as possible before you do
    -- induction; induction does some pretty complicated
    -- proof state manipulation
    induction h with
    | nv_0 =>
      intro ⟨ witness, contradiction ⟩
      contradiction
    | nv_succ nv ih =>
      rename_i t
      intro ⟨ witness, c ⟩
      cases c
      rename_i t' s
      apply ih
      exists t'
```

We can prove our step relation is deterministic:

```savedLean
def deterministic (R : relation X) :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2

theorem step_deterministic: deterministic step := by
  sorry
```

Exercise: is there a way to make this proof nice and not
painful?

# Type systems

```savedLean
inductive ty : Type where
| Bool : ty
| Nat : ty

inductive has_type : tm -> ty -> Prop where
| t_true : has_type {{true}} .Bool
| t_false : has_type {{false}} .Bool
| t_ite :
  ∀ g thn els : tm,
  has_type g .Bool ->
  has_type thn t ->
  has_type els t ->
  has_type {{if [g] then [thn] else [els]}} t
| t_zro : has_type {{zero}} .Nat
| t_succ :
  ∀ t : tm,
  has_type t .Nat ->
  has_type {{succ [t]}} .Nat
| t_pred :
  ∀ t,
  has_type t .Nat ->
  has_type {{pred [t]}} .Nat
| t_zero? :
  ∀ t,
  has_type t .Nat ->
  has_type {{zero? [t]}} .Bool
```

Some useful metatheoretic properties of the
type system:

```savedLean
theorem bool_canonical :
  ∀ t,
  has_type t .Bool -> value t -> bvalue t := by
  intro t ty v
  cases v with
  | inl => assumption
  | inr =>
    rename_i h
    cases ty <;> contradiction

theorem num_canonical :
  ∀ t,
  has_type t .Nat -> value t -> nvalue t := by
  intro t ty v
  cases v with
  | inl => cases ty <;> contradiction
  | inr => assumption
```

Now let's prove *syntactic type soundness*. Formally, syntactic type soundness
says a well-typed term never gets stuck when evaluated under its small-step
operational semantics. To establish syntactic type soundness, one typically
proves two lemmas:

* *Progress lemma*: A well-typed term is either a value or
  it can take a step.
* *Preservation lemma*: If a well-typed term can take a step,
  the term it steps to is well-typed at the same
  type.

Let's prove each of these lemmas individually and then combine them
to prove type syntactic type soundness.

```savedLean
theorem progress :
  ∀ e : tm,
  has_type e τ →
  (value e) ∨ (∃ e', step e e') := by
  intro e ty
  induction ty with
  | t_true =>
    left
    constructor
    constructor
  | t_false =>
    left
    constructor
    constructor
  | t_ite g thn els tyg tythn tyels =>
    rename_i ih_g ih_thn ih_els
    cases ih_g
    · -- g is a value, use canonical forms to
      -- extract it and take a step
      rename_i val_g
      obtain bool_g : bvalue g :=
        by apply bool_canonical g tyg val_g
      cases bool_g
      · right
        exists thn
        constructor
      · right
        exists els
        constructor
    · -- g is not a value, it can step by IH
      rename_i g_steps
      right
      obtain ⟨ g', g_steps ⟩ := g_steps
      exists {{if [g'] then [thn] else [els]}}
      apply step.st_if
      assumption
  | t_zro =>
    left
    right
    constructor
  | t_succ e' ty ih =>
    cases ih
    · -- e' is a value, use canonical forms lemma
      rename_i val_e'
      obtain num_e' : nvalue e' :=
        by apply num_canonical e' ty val_e'
      left
      right
      constructor
      assumption
    · -- e' is not a value, it can step by IH
      rename_i e'_steps
      right
      obtain ⟨ e'', e''_steps ⟩ := e'_steps
      exists {{ succ [e''] }}
      constructor
      assumption
  | t_zero? e ty ih =>
    cases ih
    · -- e is a value
      rename_i v
      right
      -- v is a value, step depending on if it's
      -- 0 or succ v'
      obtain num_v : nvalue e :=
        by apply num_canonical e ty v
      cases num_v
      · -- step {{ zero? zero }} -> true
        exists {{true}}
        constructor
      · -- step {{zero? (succ v)}} -> false
        rename_i e' e'_v
        exists {{false}}
        constructor
        assumption
    · -- e is not a value; take a step
      rename_i e' e_steps
      right
      obtain ⟨ e', e'_steps ⟩ := e_steps
      exists {{ zero? [e'] }}
      apply step.st_zero?
      assumption
  | t_pred e ty ih =>
    cases ih
    · -- e is a value. use canonical forms
      rename_i v
      obtain num_e : nvalue e :=
        by apply num_canonical e ty v
      cases num_e
      · -- e = zero, pred zero -> zero
        right
        exists {{zero}}
        apply step.st_pred0
      · -- e = succ e', pred (succ e') -> e'
        rename_i e' ty_e'
        right
        exists e'
        apply step.st_pred_succ
        assumption
    · -- e is not a value, it can step by IH
      rename_i e_steps
      right
      obtain ⟨ e', steps_e_e' ⟩ := e_steps
      exists {{ pred [e'] }}
      apply step.st_pred
      assumption
```

```savedLean
theorem preservation :
  ∀ e : tm,
  step e e' ->
  has_type e τ ->
  has_type e' τ := by
  intro e step_e_e' ty
  -- here we must use `generalizing`, since we want
  -- e' to vary during induction and we've already
  -- introduced it. We could accomplish the same
  -- thing by using the `revert e'` tactic, which
  -- moves `e'` back into the premise, but using
  -- `generalizing` is cleaner.
  induction ty generalizing e' with
  | t_true => cases step_e_e'
  | t_false => cases step_e_e'
  | t_zro => cases step_e_e'
  | t_ite g thn els tyg tythn tyels ihg ihthn ihels =>
    cases step_e_e' with
    | st_if_true | st_if_false => assumption
    | st_if =>
      rename_i g' step_g_g'
      obtain g'_bool : has_type g' .Bool := by
        apply ihg
        assumption
      apply has_type.t_ite
      apply ihg
      assumption
      assumption
      assumption
  | t_succ e ty ih =>
    cases step_e_e' with
    | st_succ =>
      rename_i e' step_e_e'
      apply has_type.t_succ
      apply ih
      assumption
  | t_pred e ty ih =>
    cases step_e_e' with
    | st_pred =>
      rename_i e' step_e_e'
      apply has_type.t_pred
      apply ih
      assumption
    | st_pred0 =>
      assumption
    | st_pred_succ =>
      cases ty
      assumption
  | t_zero? e ty ih =>
    cases step_e_e' with
    | st_zero? =>
      rename_i e' step_e_e'
      apply has_type.t_zero?
      apply ih
      assumption
    | st_zero?_succ => constructor
    | st_zero?_zero => constructor

```

```savedLean
inductive multi {X : Type} (R : relation X) : relation X where
  | multi_refl : ∀ (x : X), multi R x x
  | multi_step : ∀ (x y z : X),
                    R x y →
                    multi R y z →
                    multi R x z
```

```savedLean
theorem syntactic_type_safety :
  ∀ e : tm,
  has_type e τ →
  multi step e e' →
  ¬ (stuck e') := by
  intro e ty e_multi_e'
  -- first apply preservation to show e' is well-typed
  obtain ty_e' : has_type e' τ := by
    induction e_multi_e' with
    | multi_refl =>
      assumption
    | multi_step x y z x_step_y y_multistep_z ih =>
      apply ih
      apply preservation
      assumption
      assumption
  intro ⟨ witness, contradiction ⟩
  -- now apply preservation to show e' must take a step
  -- or is a value, conclude by contradiction
  obtain progr : (value e') ∨ (∃ e'', step e' e'')  := by
    apply _root_.progress
    assumption
  cases progr <;> contradiction
```
