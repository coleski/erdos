import Mathlib

open Filter Finset
open scoped Topology

namespace Erdos168

def TripleFree (A : Set ℕ) : Prop :=
  ∀ x : ℕ, 0 < x → ¬(x ∈ A ∧ 2*x ∈ A ∧ 3*x ∈ A)

def Positive (A : Set ℕ) : Prop := ∀ x ∈ A, 0 < x

noncomputable def initialSegment (A : Set ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (fun x => x ∈ A)

noncomputable def count (A : Set ℕ) (N : ℕ) : ℕ := (initialSegment A N).card

noncomputable def density (A : Set ℕ) (N : ℕ) : ℝ := count A N / (N : ℝ)

def HasNaturalDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (density A) atTop (nhds d)

noncomputable def upperDensity (A : Set ℕ) : ℝ := limsup (density A) atTop

noncomputable def candidates (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter (fun S => TripleFree (S : Set ℕ))

noncomputable def extremal (N : ℕ) : ℕ := (candidates N).sup Finset.card

noncomputable def extremalRatio (N : ℕ) : ℝ := extremal N / (N : ℝ)

noncomputable def upperExtremal : ℝ := limsup extremalRatio atTop

def rootAt (K i : ℕ) : ℕ := 18*K + 6*i + 1

def roots (K : ℕ) : Finset ℕ := (Finset.range K).image (rootAt K)

theorem rootAt_injective (K : ℕ) : Function.Injective (rootAt K) := by
  intro i j h
  unfold rootAt at h
  omega

theorem card_roots (K : ℕ) : (roots K).card = K := by
  rw [roots, Finset.card_image_of_injective _ (rootAt_injective K), Finset.card_range]

theorem mem_roots {K m : ℕ} : m ∈ roots K ↔ ∃ i < K, m = rootAt K i := by
  simp [roots, eq_comm]

theorem rootAt_properties {K i : ℕ} (hi : i < K) :
    0 < rootAt K i ∧ 18*K < rootAt K i ∧ rootAt K i < 24*K ∧
    rootAt K i % 2 = 1 ∧ rootAt K i % 3 = 1 := by
  unfold rootAt
  omega

theorem mem_prefix {A : Set ℕ} {N x : ℕ} :
    x ∈ initialSegment A N ↔ 1 ≤ x ∧ x ≤ N ∧ x ∈ A := by
  classical
  simp [initialSegment, and_assoc]

theorem tripleFree_mono {A B : Set ℕ} (hB : TripleFree B) (hAB : A ⊆ B) :
    TripleFree A := by
  intro x hx h
  exact hB x hx ⟨hAB h.1, hAB h.2.1, hAB h.2.2⟩

theorem count_le (A : Set ℕ) (N : ℕ) : count A N ≤ N := by
  classical
  have h := Finset.card_le_card (Finset.filter_subset (fun x => x ∈ A) (Finset.Icc 1 N))
  simpa [count, initialSegment, Nat.card_Icc] using h

theorem density_nonneg (A : Set ℕ) (N : ℕ) : 0 ≤ density A N := by
  unfold density
  positivity

theorem density_le_one (A : Set ℕ) (N : ℕ) : density A N ≤ 1 := by
  by_cases hN : N = 0
  · simp [density, hN]
  · unfold density
    apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hN)).2
    exact_mod_cast count_le A N

theorem mem_candidates {N : ℕ} {S : Finset ℕ} :
    S ∈ candidates N ↔ S ⊆ Finset.Icc 1 N ∧ TripleFree (S : Set ℕ) := by
  classical
  simp [candidates]

theorem empty_mem_candidates (N : ℕ) : ∅ ∈ candidates N := by
  rw [mem_candidates]
  simp [TripleFree]

theorem extremal_witness (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ TripleFree (S : Set ℕ) ∧ S.card = extremal N := by
  obtain ⟨S, hS, heq⟩ := Finset.exists_mem_eq_sup (candidates N)
    ⟨∅, empty_mem_candidates N⟩ Finset.card
  exact ⟨S, (mem_candidates.mp hS).1, (mem_candidates.mp hS).2, heq.symm⟩

theorem card_le_extremal {N : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hT : TripleFree (S : Set ℕ)) :
    S.card ≤ extremal N := by
  exact Finset.le_sup (mem_candidates.mpr ⟨hS, hT⟩)

theorem extremal_le (N : ℕ) : extremal N ≤ N := by
  obtain ⟨S, hS, _, heq⟩ := extremal_witness N
  have h := Finset.card_le_card hS
  simpa [heq, Nat.card_Icc] using h

theorem count_le_extremal {A : Set ℕ} (hA : TripleFree A) (N : ℕ) :
    count A N ≤ extremal N := by
  apply card_le_extremal
  · intro x hx
    exact Finset.mem_Icc.mpr ⟨(mem_prefix.mp hx).1, (mem_prefix.mp hx).2.1⟩
  · apply tripleFree_mono hA
    intro x hx
    exact (mem_prefix.mp hx).2.2

/-- The explicit original infinite-density comparison, not irrationality. -/
def InfiniteDensityComparison : Prop :=
  ∃ B : Set ℕ, Positive B ∧ B.Infinite ∧ TripleFree B ∧
    ∀ (A : Set ℕ) (d : ℝ), Positive A → TripleFree A → HasNaturalDensity A d →
      d < upperDensity B

end Erdos168
