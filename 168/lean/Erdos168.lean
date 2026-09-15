import Erdos168Finite
import Erdos168Limit

namespace Erdos168

theorem finiteGap : FiniteGap := fun _ hA K => finite_two_scale_gap hA K

/-- A uniform separation between every natural density and an attained upper density. -/
theorem uniform_density_separation :
    ∃ B : Set ℕ, Positive B ∧ B.Infinite ∧ TripleFree B ∧
      upperDensity B = upperExtremal ∧
      ∀ (A : Set ℕ) (d : ℝ), Positive A → TripleFree A → HasNaturalDensity A d →
        d ≤ upperDensity B - 1/192 := by
  obtain ⟨B, hpos, hfree, heq⟩ := exists_upper_extremal
  have hinf : B.Infinite := by
    by_contra h
    have hz := finite_upper_density_zero (Set.not_infinite.mp h)
    have hp := upperExtremal_pos_of_finiteGap finiteGap
    linarith
  refine ⟨B, hpos, hinf, hfree, heq, ?_⟩
  intro A d _ hA hd
  rw [heq]
  exact natural_gap_of_finiteGap finiteGap hA hd

/-- Affirmative answer to the original infinite-density comparison. -/
theorem infinite_density_comparison : InfiniteDensityComparison :=
  comparison_of_finiteGap finiteGap

#print axioms uniform_density_separation
#print axioms infinite_density_comparison

end Erdos168
