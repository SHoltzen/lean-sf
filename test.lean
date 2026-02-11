import TextbookTemplate
open TextbookTemplate

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
    · -- g is a value, use canonical forms to extract it and take a step
      rename_i val_g
      obtain bool_g : bvalue g := by apply bool_canonical g tyg val_g
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
      obtain num_e' : nvalue e' := by apply num_canonical e' ty val_e'
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
      obtain num_v : nvalue e := by apply num_canonical e ty v
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
      obtain num_e : nvalue e := by apply num_canonical e ty v
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

inductive multi {X : Type} (R : relation X) : relation X where
  | multi_refl : ∀ (x : X), multi R x x
  | multi_step : ∀ (x y z : X),
                    R x y →
                    multi R y z →
                    multi R x z

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
    apply progress
    assumption
  cases progr <;> contradiction
