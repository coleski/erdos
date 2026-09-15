import Erdos168Core

open Filter Finset
open scoped Topology

namespace Erdos168

theorem upper_ratio_nonneg (N : ℕ) : 0 ≤ extremalRatio N := by
  unfold extremalRatio
  positivity

theorem upper_ratio_le_one (N : ℕ) : extremalRatio N ≤ 1 := by
  by_cases h : N = 0
  · simp [extremalRatio, h]
  · apply (div_le_one (show (0 : ℝ) < N by exact_mod_cast Nat.pos_of_ne_zero h)).2
    exact_mod_cast extremal_le N

theorem upper_ratio_bounded : atTop.IsBoundedUnder (· ≤ ·) extremalRatio :=
  ⟨1, by simpa using (Filter.Eventually.of_forall upper_ratio_le_one :
    ∀ᶠ N in (atTop : Filter ℕ), extremalRatio N ≤ 1)⟩

theorem upper_ratio_cobounded : atTop.IsCoboundedUnder (· ≤ ·) extremalRatio := by
  exact (show atTop.IsBoundedUnder (· ≥ ·) extremalRatio from
    ⟨0, by simpa using (Filter.Eventually.of_forall upper_ratio_nonneg :
      ∀ᶠ N in (atTop : Filter ℕ), 0 ≤ extremalRatio N)⟩).isCobounded_le

private theorem next_upper_exists (j T : ℕ) :
    ∃ N : ℕ, max (j+1) ((j+1)*(3*T)) < N ∧
      upperExtremal - 1 / ((j:ℝ)+1) < extremalRatio N := by
  have hp : (0:ℝ) < 1 / ((j:ℝ)+1) := by positivity
  have hf := frequently_lt_of_lt_limsup upper_ratio_cobounded
    (show upperExtremal - 1 / ((j:ℝ)+1) < limsup extremalRatio atTop by
      unfold upperExtremal; linarith)
  obtain ⟨N, hN, hr⟩ := (hf.and_eventually
    (eventually_gt_atTop (max (j+1) ((j+1)*(3*T))))).exists
  exact ⟨N, hr, hN⟩

noncomputable def upperNext (j T : ℕ) : ℕ :=
  Classical.choose (next_upper_exists j T)

theorem upperNext_spec (j T : ℕ) :
    max (j+1) ((j+1)*(3*T)) < upperNext j T ∧
      upperExtremal - 1 / ((j:ℝ)+1) < extremalRatio (upperNext j T) :=
  Classical.choose_spec (next_upper_exists j T)

noncomputable def upperCut : ℕ → ℕ
  | 0 => 0
  | j+1 => upperNext j (upperCut j)

theorem upperCut_step (j : ℕ) : upperCut j < upperCut (j+1) := by
  have h := (upperNext_spec j (upperCut j)).1
  change upperCut j < upperNext j (upperCut j)
  have hmul : upperCut j ≤ (j+1)*(3*upperCut j) := by nlinarith
  exact lt_of_le_of_lt (hmul.trans (le_max_right _ _)) h

theorem upperCut_strict : StrictMono upperCut := strictMono_nat_of_lt_succ upperCut_step

noncomputable def upperExt (N : ℕ) : Finset ℕ :=
  Classical.choose (extremal_witness N)

theorem upperExt_spec (N : ℕ) :
    upperExt N ⊆ Finset.Icc 1 N ∧ TripleFree (upperExt N : Set ℕ) ∧
      (upperExt N).card = extremal N :=
  Classical.choose_spec (extremal_witness N)

noncomputable def upperBlock (j : ℕ) : Finset ℕ :=
  (upperExt (upperCut (j+1))).filter (fun x => 3*upperCut j < x)

def upperSet : Set ℕ := {x | ∃ j, x ∈ upperBlock j}

theorem upperBlock_bounds {j x : ℕ} (hx : x ∈ upperBlock j) :
    0 < x ∧ 3*upperCut j < x ∧ x ≤ upperCut (j+1) := by
  classical
  obtain ⟨hs, hl⟩ := Finset.mem_filter.mp hx
  have hb := Finset.mem_Icc.mp ((upperExt_spec _).1 hs)
  exact ⟨by omega, hl, hb.2⟩

theorem upperSet_positive : Positive upperSet := by
  rintro x ⟨j, hj⟩
  exact (upperBlock_bounds hj).1

private theorem upperBlock_same {i j x y : ℕ}
    (hx : x ∈ upperBlock i) (hy : y ∈ upperBlock j)
    (hxy : x ≤ y) (hyx : y ≤ 3*x) : i = j := by
  obtain ⟨_, hxl, hxu⟩ := upperBlock_bounds hx
  obtain ⟨_, hyl, hyu⟩ := upperBlock_bounds hy
  rcases lt_trichotomy i j with hij | hij | hij
  · have hm := upperCut_strict.monotone (Nat.succ_le_of_lt hij)
    change upperCut (i+1) ≤ upperCut j at hm
    omega
  · exact hij
  · have hm := upperCut_strict.monotone (Nat.succ_le_of_lt hij)
    change upperCut (j+1) ≤ upperCut i at hm
    omega

theorem upperSet_tripleFree : TripleFree upperSet := by
  rintro x hx ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩⟩
  have hij := upperBlock_same hi hj (by omega) (by omega)
  have hik := upperBlock_same hi hk (by omega) (by omega)
  subst j
  subst k
  exact (upperExt_spec _).2.1 x hx
    ⟨(Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hj).1,
      (Finset.mem_filter.mp hk).1⟩

theorem upperBlock_large (j : ℕ) :
    extremal (upperCut (j+1)) ≤ (upperBlock j).card + 3*upperCut j := by
  classical
  let S := upperExt (upperCut (j+1))
  have hsmall : (S.filter (fun x => ¬ 3*upperCut j < x)).card ≤ 3*upperCut j := by
    have hsub : S.filter (fun x => ¬ 3*upperCut j < x) ⊆ Finset.Icc 1 (3*upperCut j) := by
      intro x hx
      obtain ⟨hs, hh⟩ := Finset.mem_filter.mp hx
      have hp := Finset.mem_Icc.mp ((upperExt_spec _).1 hs)
      exact Finset.mem_Icc.mpr ⟨hp.1, by omega⟩
    have hc := Finset.card_le_card hsub
    simpa [Nat.card_Icc] using hc
  have hcard := S.card_filter_add_card_filter_not (fun x => 3*upperCut j < x)
  rw [(upperExt_spec _).2.2] at hcard
  change extremal (upperCut (j+1)) ≤
    (S.filter (fun x => 3*upperCut j < x)).card + 3*upperCut j
  omega

theorem upperSet_count_large (j : ℕ) :
    extremal (upperCut (j+1)) ≤ count upperSet (upperCut (j+1)) + 3*upperCut j := by
  have hs : upperBlock j ⊆ initialSegment upperSet (upperCut (j+1)) := by
    intro x hx
    obtain ⟨hp, _, hu⟩ := upperBlock_bounds hx
    exact mem_prefix.mpr ⟨by omega, hu, ⟨j, hx⟩⟩
  have hc := Finset.card_le_card hs
  exact (upperBlock_large j).trans (Nat.add_le_add_right hc _)

theorem upperSet_density_large (j : ℕ) :
    upperExtremal - 2 / ((j:ℝ)+1) < density upperSet (upperCut (j+1)) := by
  let N := upperCut (j+1)
  let T := upperCut j
  have hnraw := (upperNext_spec j T).1
  have hn_nat : j+1 < N := lt_of_le_of_lt (le_max_left _ _) hnraw
  have hm_nat : (j+1)*(3*T) < N := lt_of_le_of_lt (le_max_right _ _) hnraw
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hj : (0:ℝ) < (j:ℝ)+1 := by positivity
  have hm : ((3*T:ℕ):ℝ)*((j:ℝ)+1) < (N:ℝ) := by
    have hh : ((j:ℝ)+1)*((3*T:ℕ):ℝ) < (N:ℝ) := by exact_mod_cast hm_nat
    nlinarith
  have hloss : ((3*T:ℕ):ℝ)/(N:ℝ) < 1/((j:ℝ)+1) := by
    apply (div_lt_div_iff₀ hn hj).2
    simpa using hm
  have hc : (extremal N:ℝ) ≤ (count upperSet N:ℝ) + ((3*T:ℕ):ℝ) := by
    exact_mod_cast upperSet_count_large j
  have hd : extremalRatio N ≤ density upperSet N + ((3*T:ℕ):ℝ)/(N:ℝ) := by
    unfold extremalRatio density
    rw [← add_div]
    exact div_le_div_of_nonneg_right hc (le_of_lt hn)
  have hr := (upperNext_spec j T).2
  change upperExtremal - 1/((j:ℝ)+1) < extremalRatio N at hr
  change upperExtremal - 2/((j:ℝ)+1) < density upperSet N
  have heq : 2/((j:ℝ)+1) = 1/((j:ℝ)+1) + 1/((j:ℝ)+1) := by ring
  linarith

theorem density_bounded (A : Set ℕ) : atTop.IsBoundedUnder (· ≤ ·) (density A) :=
  ⟨1, by simpa using (Filter.Eventually.of_forall (density_le_one A) :
    ∀ᶠ N in (atTop : Filter ℕ), density A N ≤ 1)⟩

theorem density_cobounded (A : Set ℕ) : atTop.IsCoboundedUnder (· ≤ ·) (density A) := by
  exact (show atTop.IsBoundedUnder (· ≥ ·) (density A) from
    ⟨0, by simpa using (Filter.Eventually.of_forall (density_nonneg A) :
      ∀ᶠ N in (atTop : Filter ℕ), 0 ≤ density A N)⟩).isCobounded_le

theorem upperDensity_le_upperExtremal {A : Set ℕ} (hA : TripleFree A) :
    upperDensity A ≤ upperExtremal := by
  apply limsup_le_limsup _ (density_cobounded A) upper_ratio_bounded
  exact Filter.Eventually.of_forall fun N =>
    div_le_div_of_nonneg_right (by exact_mod_cast count_le_extremal hA N) (by positivity)

theorem upperSet_attains : upperDensity upperSet = upperExtremal := by
  apply le_antisymm (upperDensity_le_upperExtremal upperSet_tripleFree)
  apply le_limsup_of_le (density_bounded upperSet)
  intro b hb
  by_contra h
  have hg : 0 < upperExtremal - b := by linarith
  obtain ⟨j₀, hj₀⟩ := exists_nat_one_div_lt (show 0 < (upperExtremal-b)/2 by positivity)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hb
  let j := max j₀ K
  have hle : 1/((j:ℝ)+1) ≤ 1/((j₀:ℝ)+1) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right (le_max_left j₀ K) 1
  have hsmall : 2/((j:ℝ)+1) < upperExtremal-b := by
    rw [show 2/((j:ℝ)+1) = 2*(1/((j:ℝ)+1)) by ring]
    linarith
  have hn : K ≤ upperCut (j+1) := by
    have hh := (upperNext_spec j (upperCut j)).1
    have hk : K ≤ j := le_max_right _ _
    change K ≤ upperNext j (upperCut j)
    omega
  have hbound := hK _ hn
  have hlarge := upperSet_density_large j
  linarith

/-- Attainment of the finite extremal limsup, without assuming its convergence. -/
theorem exists_upper_extremal :
    ∃ B : Set ℕ, Positive B ∧ TripleFree B ∧ upperDensity B = upperExtremal :=
  ⟨upperSet, upperSet_positive, upperSet_tripleFree, upperSet_attains⟩

#print axioms exists_upper_extremal

end Erdos168
