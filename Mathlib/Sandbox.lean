import Mathlib

variable {A K B E C F : Type*}
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [IsIntegrallyClosed A]
  [CommRing B] [Field E] [Algebra B E] [IsFractionRing B E]
  [CommRing C] [Field F] [Algebra C F] [IsFractionRing C F]
  [Algebra K E] [Algebra K F] [Algebra F E] [IsScalarTower K F E] [FiniteDimensional K E]
  [Algebra.IsSeparable K E]
  [Algebra A F] [IsScalarTower A K F] [IsIntegralClosure C A F]
  [Algebra A E] [IsScalarTower A K E] [IsIntegralClosure B A E]
  [Algebra A B] [IsScalarTower A B E]
  [Algebra C B] [Algebra C E] [IsScalarTower C F E] [IsScalarTower C B E]
  [Algebra A C] [IsScalarTower A K F] [IsScalarTower A C F]
  [IsDedekindDomain A]
  [IsIntegrallyClosed C]
  [FiniteDimensional F E]
  [IsIntegralClosure B C E]
  [Algebra.IsSeparable F E]
  [IsDedekindDomain B]
  [IsDedekindDomain C]
  [FiniteDimensional K F]
  [Algebra.IsSeparable K F]
  [NoZeroSMulDivisors C B]

open nonZeroDivisors

set_option maxHeartbeats 1000000 in
example : 1 = 0 := by
  let BEK := FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ E)
--  let BEK := Submodule.traceDual A K (1 : Submodule B E)
  let BEF := FractionalIdeal.dual C F (1 : FractionalIdeal B⁰ E)
--  let BEF := Submodule.traceDual C F (1 : Submodule B E)
  let CFK₀ := FractionalIdeal.dual A K (1 : FractionalIdeal C⁰ F)
  have h₀ : C⁰ ≤ Submonoid.comap (algebraMap C B) B⁰ := by
    refine nonZeroDivisors_le_comap_nonZeroDivisors_of_injective (algebraMap C B) ?_
    refine NoZeroSMulDivisors.iff_algebraMap_injective.mp ?_
    infer_instance
  let CFK : FractionalIdeal B⁰ E := FractionalIdeal.extended E h₀ CFK₀
  have : BEK = BEF * CFK := by
    unfold BEK BEF CFK CFK₀
    apply le_antisymm
    · intro b hb
      dsimp at hb ⊢
      rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_dual] at hb
      rw [FractionalIdeal.mem_coe]
      rw [← FractionalIdeal.dual_inv, FractionalIdeal.mem_dual]
      


      sorry
    refine (FractionalIdeal.le_dual_iff A K ?_).mp ?_
    · sorry
    · intro z hz
      dsimp at hz ⊢
      rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_dual] at hz ⊢
      · intro x hx
        rw [FractionalIdeal.mem_extended_iff] at hx
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
        · sorry

        · simp
        · rintro _ _ _ _ ⟨x, hx⟩ ⟨y, hy⟩
          rw [map_add, ← hx, ← hy, ← map_add]
          exact ⟨x + y, rfl⟩
        · rintro b n hn ⟨y, hy⟩
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hn
          · rintro _ ⟨t, ht, rfl⟩
            have : (IsLocalization.map E (algebraMap C B) h₀) t = algebraMap F E t := sorry
            rw [this]
            simp
            rw [Algebra.smul_def, ← Algebra.trace_trace (S := F)]
            have : (algebraMap B E) b * (z * (algebraMap F E) t) =
              t • ((algebraMap B E b) * z) := sorry
            rw [this, map_smul, mul_comm]
            simp at hz
            specialize hz (algebraMap B E b) sorry
            obtain ⟨l, hl⟩ := hz
            rw [← hl]
            simp at hy


            sorry
          · sorry
          · sorry
          · sorry
      · sorry
      · exact one_ne_zero

#exit
    ext x


--    rw [FractionalIdeal.mul_def]
    simp [FractionalIdeal.mem_dual]
    constructor
    · intro h
      rw [← FractionalIdeal.mem_coe]
      simp

      sorry
    · intro hx
      rw [← FractionalIdeal.mem_coe] at hx
      simp at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro m hm n hn
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hn
        · rintro _ ⟨x, hx, rfl⟩ a ha
          rw [FractionalIdeal.mem_one_iff] at ha
          obtain ⟨y, rfl⟩ := ha
          rw [Submodule.mem_traceDual] at hm
          simp at hm
          obtain ⟨z, hz⟩ := hm y
          rw [SetLike.mem_coe, FractionalIdeal.mem_dual] at hx
          simp at hx
          specialize hx (algebraMap C F z) sorry
          obtain ⟨t, ht⟩ := hx
          refine ⟨t, ?_⟩
          rw [← Algebra.trace_trace (S := F)]
          have : m * (IsLocalization.map E (algebraMap C B) this) x * (algebraMap B E y) =
              x • ((algebraMap B E y) * m) := by
            have : IsLocalization (Algebra.algebraMapSubmonoid B C⁰) E := by
              exact IsIntegralClosure.isLocalization_of_isSeparable C F E B
            have := localizationAlgebraMap_def (R := C) (S := B) (Sₘ := E) (Rₘ := F) (M := C⁰)

            erw [← localizationAlgebraMap_def]
            rw [Algebra.smul_def]
            rw [mul_comm _ m, ← mul_assoc, mul_comm _ m]
            congr
            sorry
          rw [this, map_smul, mul_comm, ← hz, smul_eq_mul, ht]
          exact Ne.symm (zero_ne_one' (FractionalIdeal C⁰ F))
        · intro _ _
          refine ⟨0, by simp⟩
        · intro x y _ _ hx hy a ha
          obtain ⟨x₁, hx₁⟩ := hx a ha
          obtain ⟨y₁, hy₁⟩ := hy a ha
          refine ⟨x₁ + y₁, ?_⟩
          simp [hx₁, hy₁, mul_add, add_mul, map_add]
        · intro b x _ hx a ha
          obtain ⟨x₁, hx₁⟩ := hx a ha
          rw [Algebra.smul_def]

          sorry
      · sorry
