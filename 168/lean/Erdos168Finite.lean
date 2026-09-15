import Erdos168Core

set_option maxHeartbeats 2000000

open Finset

namespace Erdos168

theorem root_properties {K m : ℕ} (hm : m ∈ roots K) :
    0 < m ∧ 18*K < m ∧ m < 24*K ∧ m % 2 = 1 ∧ m % 3 = 1 := by
  obtain ⟨i, hi, rfl⟩ := mem_roots.mp hm
  exact rootAt_properties hi

theorem root_mid_isolated {K m x : ℕ} (hm : m ∈ roots K)
    (hx : 3*x ≤ 48*K) : x ≠ 2*m ∧ 2*x ≠ 2*m ∧ 3*x ≠ 2*m := by
  have hp := root_properties hm
  omega

theorem root_good_closed {K m x v : ℕ} (hm : m ∈ roots K)
    (hx : 3*x ≤ 144*K)
    (hv : v = m ∨ v = 3*m ∨ v = 4*m ∨ v = 6*m)
    (he : x = v ∨ 2*x = v ∨ 3*x = v) : x = m ∨ x = 2*m := by
  have hp := root_properties hm
  rcases hv with rfl | rfl | rfl | rfl <;>
    rcases he with h | h | h <;> omega

theorem root_mid_not_good {K m n v : ℕ} (hm : m ∈ roots K)
    (hn : n ∈ roots K) (hv : v = m ∨ v = 3*m ∨ v = 4*m ∨ v = 6*m) :
    2*n ≠ v := by
  have hp := root_properties hm
  have hq := root_properties hn
  rcases hv with rfl | rfl | rfl | rfl <;> omega

theorem insert_isolated {K m : ℕ} {S : Finset ℕ}
    (hm : m ∈ roots K) (hS : S ⊆ Icc 1 (48*K))
    (hfree : TripleFree (S : Set ℕ)) :
    (insert (2*m) S) ⊆ Icc 1 (48*K) ∧
      TripleFree ((insert (2*m) S : Finset ℕ) : Set ℕ) := by
  classical
  have hp := root_properties hm
  have hb : insert (2*m) S ⊆ Icc 1 (48*K) := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_Icc.mpr (by omega)
    · exact hS hx
  refine ⟨hb, ?_⟩
  intro x hx ht
  have hbound := (mem_Icc.mp (hb ht.2.2)).2
  have hi := root_mid_isolated hm hbound
  apply hfree x hx
  exact ⟨(mem_insert.mp ht.1).resolve_left hi.1,
    (mem_insert.mp ht.2.1).resolve_left hi.2.1,
    (mem_insert.mp ht.2.2).resolve_left hi.2.2⟩

theorem root_swap {K m : ℕ} {T : Finset ℕ}
    (hm : m ∈ roots K) (hT : T ⊆ Icc 1 (144*K))
    (hfree : TripleFree (T : Set ℕ)) (hmid : 2*m ∈ T) :
    ∃ U : Finset ℕ, U ⊆ Icc 1 (144*K) ∧ TripleFree (U : Set ℕ) ∧
      U.card = T.card + 1 ∧
      ∀ n ∈ roots K, n ≠ m → (2*n ∈ U ↔ 2*n ∈ T) := by
  classical
  have hp := root_properties hm
  have hp1 : m ∉ T ∨ 3*m ∉ T := by
    by_contra h
    push Not at h
    exact hfree m hp.1 ⟨h.1, hmid, h.2⟩
  have hp2 : 4*m ∉ T ∨ 6*m ∉ T := by
    by_contra h
    push Not at h
    apply hfree (2*m) (by omega)
    simpa [← Nat.mul_assoc] using And.intro hmid (And.intro h.1 h.2)
  obtain ⟨a, ha, hna⟩ : ∃ a, (a = m ∨ a = 3*m) ∧ a ∉ T := by
    rcases hp1 with h | h
    · exact ⟨m, Or.inl rfl, h⟩
    · exact ⟨3*m, Or.inr rfl, h⟩
  obtain ⟨b, hb, hnb⟩ : ∃ b, (b = 4*m ∨ b = 6*m) ∧ b ∉ T := by
    rcases hp2 with h | h
    · exact ⟨4*m, Or.inl rfl, h⟩
    · exact ⟨6*m, Or.inr rfl, h⟩
  have hag : a = m ∨ a = 3*m ∨ a = 4*m ∨ a = 6*m :=
    ha.elim Or.inl (fun h => Or.inr (Or.inl h))
  have hbg : b = m ∨ b = 3*m ∨ b = 4*m ∨ b = 6*m :=
    Or.inr (Or.inr hb)
  have hab : a ≠ b := by rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega
  let U := insert a (insert b (T.erase (2*m)))
  have hUb : U ⊆ Icc 1 (144*K) := by
    intro x hx
    simp only [U, mem_insert, mem_erase] at hx
    rcases hx with rfl | rfl | ⟨_, hx⟩
    · exact mem_Icc.mpr (by rcases ha with rfl | rfl <;> omega)
    · exact mem_Icc.mpr (by rcases hb with rfl | rfl <;> omega)
    · exact hT hx
  have hmU : 2*m ∉ U := by
    have h1 := root_mid_not_good hm hm hag
    have h2 := root_mid_not_good hm hm hbg
    simp [U, h1, h2]
  have hUf : TripleFree (U : Set ℕ) := by
    intro x hx ht
    have hxbound := (mem_Icc.mp (hUb ht.2.2)).2
    have hold : ∀ v, v ∈ U → v = x ∨ v = 2*x ∨ v = 3*x → v ∈ T := by
      intro v hv he
      simp only [U, mem_insert, mem_erase] at hv
      rcases hv with rfl | rfl | ⟨_, hv⟩
      · have he' : x = v ∨ 2*x = v ∨ 3*x = v :=
          he.elim (fun h => Or.inl h.symm)
            (fun h => h.elim (fun h => Or.inr (Or.inl h.symm))
              (fun h => Or.inr (Or.inr h.symm)))
        have hclosed := root_good_closed hm hxbound hag he'
        rcases hclosed with rfl | rfl
        · exact False.elim (hmU ht.2.1)
        · exact False.elim (hmU ht.1)
      · have he' : x = v ∨ 2*x = v ∨ 3*x = v :=
          he.elim (fun h => Or.inl h.symm)
            (fun h => h.elim (fun h => Or.inr (Or.inl h.symm))
              (fun h => Or.inr (Or.inr h.symm)))
        have hclosed := root_good_closed hm hxbound hbg he'
        rcases hclosed with rfl | rfl
        · exact False.elim (hmU ht.2.1)
        · exact False.elim (hmU ht.1)
      · exact hv
    exact hfree x hx ⟨hold x ht.1 (Or.inl rfl),
      hold (2*x) ht.2.1 (Or.inr (Or.inl rfl)),
      hold (3*x) ht.2.2 (Or.inr (Or.inr rfl))⟩
  have hcard : U.card = T.card + 1 := by
    have haerase : a ∉ T.erase (2*m) := fun h => hna (mem_of_mem_erase h)
    have hberase : b ∉ T.erase (2*m) := fun h => hnb (mem_of_mem_erase h)
    have hains : a ∉ insert b (T.erase (2*m)) := by simp [hab, haerase]
    simp only [U, card_insert_of_notMem hains, card_insert_of_notMem hberase]
    have h := card_erase_add_one hmid
    omega
  refine ⟨U, hUb, hUf, hcard, ?_⟩
  intro n hn hnm
  have h1 := root_mid_not_good hm hn hag
  have h2 := root_mid_not_good hm hn hbg
  have h3 : 2*n ≠ 2*m := by omega
  simp [U, h1, h2, h3]

theorem upgrade_roots (K : ℕ) (P : Finset ℕ) :
    ∀ (S T : Finset ℕ), P ⊆ roots K →
      S ⊆ Icc 1 (48*K) → T ⊆ Icc 1 (144*K) →
      TripleFree (S : Set ℕ) → TripleFree (T : Set ℕ) →
      (∀ m ∈ P, (2*m ∈ S ↔ 2*m ∈ T)) →
      ∃ V W : Finset ℕ, V ⊆ Icc 1 (48*K) ∧ W ⊆ Icc 1 (144*K) ∧
        TripleFree (V : Set ℕ) ∧ TripleFree (W : Set ℕ) ∧
        S.card + T.card + P.card ≤ V.card + W.card := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      intro S T hP hS hT hfS hfT heq
      exact ⟨S, T, hS, hT, hfS, hfT, by simp⟩
  | @insert m P hnot ih =>
      intro S T hP hS hT hfS hfT heq
      have hm : m ∈ roots K := hP (mem_insert_self _ _)
      have hPrest : P ⊆ roots K := fun n hn => hP (mem_insert_of_mem hn)
      have hPeq : ∀ n ∈ P, (2*n ∈ S ↔ 2*n ∈ T) :=
        fun n hn => heq n (mem_insert_of_mem hn)
      have hPcard : (insert m P).card = P.card + 1 := card_insert_of_notMem hnot
      by_cases hmid : 2*m ∈ S
      · have hmidT : 2*m ∈ T := (heq m (mem_insert_self _ _)).mp hmid
        obtain ⟨U, hUb, hUf, hUc, hUm⟩ := root_swap hm hT hfT hmidT
        have hmatch : ∀ n ∈ P, (2*n ∈ S ↔ 2*n ∈ U) := by
          intro n hn
          have hnm : n ≠ m := by intro h; subst n; exact hnot hn
          exact (hPeq n hn).trans (hUm n (hPrest hn) hnm).symm
        obtain ⟨V, W, hV, hW, hfV, hfW, hcard⟩ :=
          ih S U hPrest hS hUb hfS hUf hmatch
        exact ⟨V, W, hV, hW, hfV, hfW, by omega⟩
      · obtain ⟨hUb, hUf⟩ := insert_isolated hm hS hfS
        have hUc : (insert (2*m) S).card = S.card + 1 := card_insert_of_notMem hmid
        have hmatch : ∀ n ∈ P, (2*n ∈ insert (2*m) S ↔ 2*n ∈ T) := by
          intro n hn
          have hnm : n ≠ m := by intro h; subst n; exact hnot hn
          have hneq : 2*n ≠ 2*m := by omega
          simpa [hneq] using hPeq n hn
        obtain ⟨V, W, hV, hW, hfV, hfW, hcard⟩ :=
          ih (insert (2*m) S) T hPrest hUb hT hUf hfT hmatch
        exact ⟨V, W, hV, hW, hfV, hfW, by omega⟩

theorem finite_two_scale_gap {A : Set ℕ} (hA : TripleFree A) (K : ℕ) :
    count A (48*K) + count A (144*K) + K ≤
      extremal (48*K) + extremal (144*K) := by
  classical
  let S := initialSegment A (48*K)
  let T := initialSegment A (144*K)
  have hS : S ⊆ Icc 1 (48*K) := by
    intro x hx
    exact mem_Icc.mpr ⟨(mem_prefix.mp hx).1, (mem_prefix.mp hx).2.1⟩
  have hT : T ⊆ Icc 1 (144*K) := by
    intro x hx
    exact mem_Icc.mpr ⟨(mem_prefix.mp hx).1, (mem_prefix.mp hx).2.1⟩
  have hfS : TripleFree (S : Set ℕ) :=
    tripleFree_mono hA (fun _ hx => (mem_prefix.mp hx).2.2)
  have hfT : TripleFree (T : Set ℕ) :=
    tripleFree_mono hA (fun _ hx => (mem_prefix.mp hx).2.2)
  have hmatch : ∀ m ∈ roots K, (2*m ∈ S ↔ 2*m ∈ T) := by
    intro m hm
    have hp := root_properties hm
    have hs : 1 ≤ 2*m ∧ 2*m ≤ 48*K := by omega
    have ht : 1 ≤ 2*m ∧ 2*m ≤ 144*K := by omega
    simp only [S, T, mem_prefix, hs.1, hs.2, ht.2, true_and]
  obtain ⟨V, W, hV, hW, hfV, hfW, hcard⟩ :=
    upgrade_roots K (roots K) S T (fun _ h => h) hS hT hfS hfT hmatch
  have hbV := card_le_extremal hV hfV
  have hbW := card_le_extremal hW hfW
  have hc := card_roots K
  change S.card + T.card + K ≤ _
  omega

end Erdos168

#print axioms Erdos168.finite_two_scale_gap
