import TextbookTemplate
open TextbookTemplate

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
