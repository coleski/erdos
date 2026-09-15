import Erdos168Upper

open Filter Finset
open scoped Topology

namespace Erdos168

def FiniteGap : Prop := ∀ (A : Set ℕ), TripleFree A → ∀ K : ℕ,
  count A (48*K) + count A (144*K) + K ≤ extremal (48*K) + extremal (144*K)

theorem natural_gap_of_finiteGap (hgap : FiniteGap) {A : Set ℕ} {d : ℝ}
    (hA : TripleFree A) (hd : HasNaturalDensity A d) :
    d ≤ upperExtremal - 1/192 := by
  by_contra h
  have hg : upperExtremal - 1/192 < d := lt_of_not_ge h
  let ε : ℝ := (d - (upperExtremal - 1/192))/4
  have he : 0 < ε := by dsimp [ε]; linarith
  have hu : ∀ᶠ N : ℕ in atTop, extremalRatio N < upperExtremal + ε :=
    eventually_lt_add_pos_of_limsup_le upper_ratio_bounded le_rfl he
  have hl : ∀ᶠ N : ℕ in atTop, d-ε < density A N :=
    hd.eventually (lt_mem_nhds (by linarith))
  obtain ⟨Nu, hNu⟩ := eventually_atTop.mp hu
  obtain ⟨Nl, hNl⟩ := eventually_atTop.mp hl
  let K := max Nu Nl + 1
  have hKnat : 0 < K := by omega
  have hK : (0:ℝ) < K := by exact_mod_cast hKnat
  have h48u := hNu (48*K) (by omega)
  have h144u := hNu (144*K) (by omega)
  have h48l := hNl (48*K) (by omega)
  have h144l := hNl (144*K) (by omega)
  have hp48 : (0:ℝ) < (48*K:ℕ) := by positivity
  have hp144 : (0:ℝ) < (144*K:ℕ) := by positivity
  have u48 := (div_lt_iff₀ hp48).mp h48u
  have u144 := (div_lt_iff₀ hp144).mp h144u
  have l48 := (lt_div_iff₀ hp48).mp h48l
  have l144 := (lt_div_iff₀ hp144).mp h144l
  have hc : (count A (48*K):ℝ) + (count A (144*K):ℝ) + (K:ℝ) ≤
      (extremal (48*K):ℝ) + (extremal (144*K):ℝ) := by
    exact_mod_cast hgap A hA K
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at u48 u144 l48 l144
  have heq : d - upperExtremal + 1/192 = 4*ε := by dsimp [ε]; ring
  have heqK := congrArg (fun x : ℝ => x*(K:ℝ)) heq
  have heK : 0 < ε*(K:ℝ) := mul_pos he hK
  nlinarith

theorem finite_natural_density_zero {A : Set ℕ} (hA : A.Finite) :
    HasNaturalDensity A 0 := by
  classical
  have hc (N : ℕ) : count A N ≤ hA.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    exact hA.mem_toFinset.mpr (mem_prefix.mp hx).2.2
  have hb (N : ℕ) : density A N ≤ (hA.toFinset.card:ℝ)/(N:ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast hc N) (by positivity)
  exact squeeze_zero (density_nonneg A) hb
    (tendsto_const_div_atTop_nhds_zero_nat (hA.toFinset.card:ℝ))

theorem finite_upper_density_zero {A : Set ℕ} (hA : A.Finite) :
    upperDensity A = 0 := by
  exact (finite_natural_density_zero hA).limsup_eq

theorem upperExtremal_pos_of_finiteGap (hgap : FiniteGap) : 0 < upperExtremal := by
  have hz : HasNaturalDensity (∅ : Set ℕ) 0 :=
    finite_natural_density_zero Set.finite_empty
  have ht : TripleFree (∅ : Set ℕ) := by simp [TripleFree]
  have hg := natural_gap_of_finiteGap hgap ht hz
  linarith

theorem comparison_of_finiteGap (hgap : FiniteGap) : InfiniteDensityComparison := by
  obtain ⟨B, hpos, hfree, heq⟩ := exists_upper_extremal
  have hinf : B.Infinite := by
    by_contra h
    have hz := finite_upper_density_zero (Set.not_infinite.mp h)
    have hp := upperExtremal_pos_of_finiteGap hgap
    linarith
  refine ⟨B, hpos, hinf, hfree, ?_⟩
  intro A d _ hA hd
  have hg := natural_gap_of_finiteGap hgap hA hd
  rw [heq]
  linarith

#print axioms natural_gap_of_finiteGap
#print axioms comparison_of_finiteGap

end Erdos168
