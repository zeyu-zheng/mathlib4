import Mathlib.Data.List.Basic

open List Function

variable {X : Type*}

def F1 (F0 : List (X → X)) : Set (X → X) := {f | ∃ l, l ⊆ F0 ∧ f = l.foldr (· ∘ ·) id}

variable {F0 : List (X → X)}

lemma comp_mem_F1 {f g : X → X} (hf : f ∈ F1 F0) (hg : g ∈ F1 F0) : f ∘ g ∈ F1 F0 := by
  obtain ⟨lf, hlf, rfl⟩ := hf
  obtain ⟨lg, hlg, rfl⟩ := hg
  refine ⟨lf ++ lg, append_subset_of_subset_of_subset hlf hlg, ?_⟩
  induction lf with
  | nil => simp
  | cons a l hl =>
    rw [foldr_cons, cons_append, foldr_cons, comp_assoc, hl]
    exact subset_of_cons_subset hlf

theorem my_theorem (fi fj : X → X) (fi_inv fj_inv : X → X) (hfi_inv : fi_inv ∈ F1 F0)
  (hfj_inv : fj_inv ∈ F1 F0) (hi : LeftInverse fi_inv fi) (hj : RightInverse fj_inv fj)
  (g : X → X) (hg : g ∉ F1 F0) : fi ∘ g ∘ fj ∉ F1 F0 := by
  by_contra! h
  have := comp_mem_F1 (comp_mem_F1 hfi_inv h) hfj_inv
  rw [← comp_assoc, hi.id, comp_assoc, comp_assoc, hj.id] at this
  contradiction
