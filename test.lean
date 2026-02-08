import TextbookTemplate
open TextbookTemplate

inductive ty : Type :=
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

theorem bool_canonical :
  ∀ t : tm, has_type t .Bool -> value t -> bvalue t := by
  intro t ty v
  cases ty with
  | t_true => constructor
  | t_false => constructor
  | t_ite =>
    sorry
