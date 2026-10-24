module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise_6_18
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_21

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}
namespace Proposition77
/- concordance: source L4433 PROPOSITION 7.7 lists effectively given -/
/-- **Proposition 7.7 (Scott 1981, PRG-19).** Scott's enumeration of `D^§`:
`V₀ = Γ`, `V_{2n+1} = 0·Xₙ`, `V_{2n+2} = 1·V_{p n} ∪ 2·V_{q n}` (`p = unpair.1`, `q = unpair.2`). -/
def Vsharp (D : NeighborhoodSystem α) (P : ComputablePresentation D) :
    ℕ → Set (List Bool × α)
  | 0 => Gamma D
  | (k + 1) =>
      if (k + 1) % 2 = 1 then
        embZero (P.X (k / 2))
      else
        embPair (Vsharp D P ((k - 1) / 2).unpair.1) (Vsharp D P ((k - 1) / 2).unpair.2)
  termination_by k => k
  decreasing_by
    · have := unpair_fst_le ((k - 1) / 2); omega
    · have := unpair_snd_le ((k - 1) / 2); omega

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- One-step unfolding of `Vsharp` at a successor index. -/
theorem Vsharp_succ (k : ℕ) :
    Vsharp D P (k + 1) =
      if (k + 1) % 2 = 1 then embZero (P.X (k / 2))
      else embPair (Vsharp D P ((k - 1) / 2).unpair.1) (Vsharp D P ((k - 1) / 2).unpair.2) := by
  rw [Vsharp]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Vsharp_even (n : ℕ) :
    Vsharp D P (2 * n + 2) = embPair (Vsharp D P n.unpair.1) (Vsharp D P n.unpair.2) := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from rfl, Vsharp_succ, ite_eq_right (by omega),
    show (2 * n + 1 - 1) / 2 = n from by omega]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Vsharp_even_inter_even (a b : ℕ) :
    Vsharp D P (2 * a + 2) ∩ Vsharp D P (2 * b + 2)
      = embPair (Vsharp D P a.unpair.1 ∩ Vsharp D P b.unpair.1)
                (Vsharp D P a.unpair.2 ∩ Vsharp D P b.unpair.2) := by
  rw [Vsharp_even, Vsharp_even, embPair_inter]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Vsharp_odd (n : ℕ) : Vsharp D P (2 * n + 1) = embZero (P.X n) := by
  rw [Vsharp_succ, ite_eq_left (by omega), show 2 * n / 2 = n from by omega]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Vsharp_odd_inter_even (a b : ℕ) :
    Vsharp D P (2 * a + 1) ∩ Vsharp D P (2 * b + 2) = ∅ := by
  rw [Vsharp_odd, Vsharp_even, embZero_inter_embPair]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Vsharp_even_inter_odd (a b : ℕ) :
    Vsharp D P (2 * a + 2) ∩ Vsharp D P (2 * b + 1) = ∅ := by
  rw [Set.inter_comm]; exact Vsharp_odd_inter_even P b a

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Vsharp_odd_inter_odd (a b : ℕ) :
    Vsharp D P (2 * a + 1) ∩ Vsharp D P (2 * b + 1) = embZero (P.X a ∩ P.X b) := by
  rw [Vsharp_odd, Vsharp_odd, embZero_inter]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Vsharp_zero : Vsharp D P 0 = Gamma D := by rw [Vsharp]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Vsharp_eq_Gamma_iff (hD : ∀ X, D.mem X → X.Nonempty) (j : ℕ) :
    Vsharp D P j = Gamma D ↔ j = 0 := by
  constructor
  · intro h
    rcases nat_shape j with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rfl
    · rw [Vsharp_odd] at h; exact absurd h (embZero_ne_Gamma D hD (P.X a))
    · rw [Vsharp_even] at h; exact absurd h (embPair_ne_Gamma D hD _ _)
  · rintro rfl; exact Vsharp_zero P

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- Every `V k` is a neighbourhood of `D^§`. -/
theorem Vsharp_mem (k : ℕ) : MemS D (Vsharp D P k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [Vsharp_zero]; exact MemS.gamma
    · -- `k ≥ 1` is odd `2n+1` or even `2n+2`, decided choice-free by `k % 2`.
      rcases (by
        rcases Nat.lt_or_ge (k % 2) 1 with h | h
        · exact Or.inr ⟨k / 2 - 1, by omega⟩
        · exact Or.inl ⟨k / 2, by omega⟩ :
          (∃ n, k = 2 * n + 1) ∨ (∃ n, k = 2 * n + 2)) with ⟨n, rfl⟩ | ⟨n, rfl⟩
      · rw [Vsharp_odd]; exact MemS.zero (P.mem_X n)
      · rw [Vsharp_even]
        exact MemS.pair (ih _ (by have := unpair_fst_le n; omega))
          (ih _ (by have := unpair_snd_le n; omega))

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Vsharp_inter_zero (n : ℕ) : Vsharp D P n ∩ Vsharp D P 0 = Vsharp D P n := by
  rw [Vsharp_zero, Set.inter_eq_left]; exact memS_subset_gamma (Vsharp_mem P n)

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- Under `∅ ∉ 𝒟`, no `V k` is empty. -/
theorem Vsharp_nonempty (hD : ∀ X, D.mem X → X.Nonempty) (k : ℕ) : (Vsharp D P k).Nonempty :=
  memS_nonempty hD (Vsharp_mem P k)

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- Every neighbourhood of `D^§` is enumerated as some `V k` (surjectivity of `V`). -/
theorem Vsharp_surj {W : Set (List Bool × α)} (hW : MemS D W) : ∃ k, Vsharp D P k = W := by
  induction hW with
  | gamma => exact ⟨0, Vsharp_zero P⟩
  | @zero X hX => obtain ⟨n, hn⟩ := P.surj hX; exact ⟨2 * n + 1, by rw [Vsharp_odd, hn]⟩
  | @pair Pp Qq _ _ ihP ihQ =>
      obtain ⟨a, ha⟩ := ihP
      obtain ⟨b, hb⟩ := ihQ
      refine ⟨2 * Nat.pair a b + 2, ?_⟩
      have h1 : (Nat.pair a b).unpair.1 = a := by rw [unpair_pair]
      have h2 : (Nat.pair a b).unpair.2 = b := by rw [unpair_pair]
      rw [Vsharp_even, h1, h2, ha, hb]

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Vsharp_zero_inter (m : ℕ) : Vsharp D P 0 ∩ Vsharp D P m = Vsharp D P m := by
  rw [Vsharp_zero, Set.inter_eq_right]; exact memS_subset_gamma (Vsharp_mem P m)

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem exists_sub_embPair_iff (hD : ∀ X, D.mem X → X.Nonempty)
    (A B : Set (List Bool × α)) :
    (∃ l, Vsharp D P l ⊆ embPair A B) ↔
      (∃ l, Vsharp D P l ⊆ A) ∧ (∃ l, Vsharp D P l ⊆ B) := by
  constructor
  · rintro ⟨l, hl⟩
    obtain ⟨Pp, Qq, hP, hQ, hWeq⟩ := memS_sub_embPair hD (Vsharp_mem P l) hl
    rw [hWeq] at hl
    obtain ⟨hPA, hQB⟩ := embPair_subset.mp hl
    obtain ⟨l1, h1⟩ := Vsharp_surj P hP
    obtain ⟨l2, h2⟩ := Vsharp_surj P hQ
    exact ⟨⟨l1, h1 ▸ hPA⟩, ⟨l2, h2 ▸ hQB⟩⟩
  · rintro ⟨⟨l1, h1⟩, ⟨l2, h2⟩⟩
    obtain ⟨l, hl⟩ := Vsharp_surj P (MemS.pair (Vsharp_mem P l1) (Vsharp_mem P l2))
    exact ⟨l, by rw [hl]; exact embPair_subset.mpr ⟨h1, h2⟩⟩

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem exists_sub_embZero_iff (hD : ∀ X, D.mem X → X.Nonempty) (Y : Set α) :
    (∃ l, Vsharp D P l ⊆ embZero Y) ↔ ∃ k, P.X k ⊆ Y := by
  constructor
  · rintro ⟨l, hl⟩
    obtain ⟨Z, hZ, hWZ⟩ := memS_sub_embZero hD (Vsharp_mem P l) hl
    rw [hWZ] at hl
    obtain ⟨k, hk⟩ := P.surj hZ
    exact ⟨k, hk ▸ embZero_subset.mp hl⟩
  · rintro ⟨k, hk⟩
    exact ⟨2 * k + 1, by rw [Vsharp_odd]; exact embZero_subset.mpr hk⟩

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

theorem dsharp_decider_spec (hD : ∀ X, D.mem X → X.Nonempty)
    (hcons : ∀ a b, fcons (Nat.pair a b) = 1 ↔ ∃ l, P.X l ⊆ P.X a ∩ P.X b)
    (heq : ∀ a b, feq (Nat.pair a b) = 1 ↔ P.X a = P.X b)
    (hinter : ∀ a b, (∃ l, P.X l ⊆ P.X a ∩ P.X b) → P.X (finter (Nat.pair a b)) = P.X a ∩ P.X b) :
    ∀ i j : ℕ,
      (consB (gOf (dsharpStep fcons feq finter) (Nat.pair i j)) = 1
          ↔ ∃ l, Vsharp D P l ⊆ Vsharp D P i ∩ Vsharp D P j) ∧
        ((∃ l, Vsharp D P l ⊆ Vsharp D P i ∩ Vsharp D P j) →
          Vsharp D P (intI (gOf (dsharpStep fcons feq finter) (Nat.pair i j)))
            = Vsharp D P i ∩ Vsharp D P j) ∧
        (eqB (gOf (dsharpStep fcons feq finter) (Nat.pair i j)) = 1
          ↔ Vsharp D P i = Vsharp D P j) := by
  have key : ∀ w : ℕ, ∀ i j : ℕ, Nat.pair i j = w →
      (consB (gOf (dsharpStep fcons feq finter) (Nat.pair i j)) = 1
          ↔ ∃ l, Vsharp D P l ⊆ Vsharp D P i ∩ Vsharp D P j) ∧
        ((∃ l, Vsharp D P l ⊆ Vsharp D P i ∩ Vsharp D P j) →
          Vsharp D P (intI (gOf (dsharpStep fcons feq finter) (Nat.pair i j)))
            = Vsharp D P i ∩ Vsharp D P j) ∧
        (eqB (gOf (dsharpStep fcons feq finter) (Nat.pair i j)) = 1
          ↔ Vsharp D P i = Vsharp D P j) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro i j hw
      rcases nat_shape i with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
      · -- i = 0 (Γ ∩ V_j = V_j)
        simp only [gOf_def]
        rw [dsharpStep_i0 fcons feq finter j]
        simp only [eqB_packT, consB_packT, intI_packT]
        refine ⟨?_, ?_, ?_⟩
        · exact ⟨fun _ => ⟨j, (Vsharp_zero_inter P j).ge⟩, fun _ => trivial⟩
        · intro _; rw [Vsharp_zero_inter P]
        · constructor
          · intro h
            have hj : j = 0 := by omega
            rw [hj]
          · intro h
            have hj : j = 0 := (Vsharp_eq_Gamma_iff P hD j).mp (h.symm.trans (Vsharp_zero P))
            omega
      · -- i = 2a+1 (leaf)
        rcases nat_shape j with rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
        · -- j = 0
          simp only [gOf_def]
          rw [dsharpStep_j0 fcons feq finter _ (by omega : 2 * a + 1 ≠ 0)]
          simp only [eqB_packT, consB_packT, intI_packT]
          refine ⟨?_, ?_, ?_⟩
          · exact ⟨fun _ => ⟨2 * a + 1, (Vsharp_inter_zero P (2 * a + 1)).ge⟩, fun _ => trivial⟩
          · intro _; exact (Vsharp_inter_zero P (2 * a + 1)).symm
          · rw [Vsharp_zero P, Vsharp_eq_Gamma_iff P hD]; omega
        · -- j = 2b+1 (leaf ∩ leaf)
          simp only [gOf_def]
          rw [dsharpStep_ll fcons feq finter a b]
          simp only [eqB_packT, consB_packT, intI_packT]
          refine ⟨?_, ?_, ?_⟩
          · rw [Vsharp_odd_inter_odd P, exists_sub_embZero_iff P hD]; exact hcons a b
          · intro hp
            rw [Vsharp_odd_inter_odd P] at hp ⊢
            rw [exists_sub_embZero_iff P hD] at hp
            rw [Vsharp_odd P, hinter a b hp]
          · rw [Vsharp_odd P, Vsharp_odd P, heq a b]
            exact ⟨fun h => by rw [h], fun h => embZero_injective h⟩
        · -- j = 2b+2 (leaf ∩ node : inconsistent)
          simp only [gOf_def]
          rw [dsharpStep_ln fcons feq finter a b]
          simp only [eqB_packT, consB_packT, intI_packT]
          refine ⟨?_, ?_, ?_⟩
          · rw [Vsharp_odd_inter_even P]
            constructor
            · intro h; exact absurd h (by decide)
            · rintro ⟨l, hl⟩
              obtain ⟨x, hx⟩ := Vsharp_nonempty P hD l
              exact absurd (hl hx) (by simp)
          · rw [Vsharp_odd_inter_even P]
            rintro ⟨l, hl⟩
            obtain ⟨x, hx⟩ := Vsharp_nonempty P hD l
            exact absurd (hl hx) (by simp)
          · rw [Vsharp_odd P, Vsharp_even P]
            constructor
            · intro h; exact absurd h (by decide)
            · intro h; exact absurd h (embZero_ne_embPair D hD (P.mem_X a) _ _)
      · -- i = 2a+2 (node)
        rcases nat_shape j with rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
        · -- j = 0
          simp only [gOf_def]
          rw [dsharpStep_j0 fcons feq finter _ (by omega : 2 * a + 2 ≠ 0)]
          simp only [eqB_packT, consB_packT, intI_packT]
          refine ⟨?_, ?_, ?_⟩
          · exact ⟨fun _ => ⟨2 * a + 2, (Vsharp_inter_zero P (2 * a + 2)).ge⟩, fun _ => trivial⟩
          · intro _; exact (Vsharp_inter_zero P (2 * a + 2)).symm
          · rw [Vsharp_zero P, Vsharp_eq_Gamma_iff P hD]; omega
        · -- j = 2b+1 (node ∩ leaf : inconsistent)
          simp only [gOf_def]
          rw [dsharpStep_nl fcons feq finter a b]
          simp only [eqB_packT, consB_packT, intI_packT]
          refine ⟨?_, ?_, ?_⟩
          · rw [Vsharp_even_inter_odd P]
            constructor
            · intro h; exact absurd h (by decide)
            · rintro ⟨l, hl⟩
              obtain ⟨x, hx⟩ := Vsharp_nonempty P hD l
              exact absurd (hl hx) (by simp)
          · rw [Vsharp_even_inter_odd P]
            rintro ⟨l, hl⟩
            obtain ⟨x, hx⟩ := Vsharp_nonempty P hD l
            exact absurd (hl hx) (by simp)
          · rw [Vsharp_even P, Vsharp_odd P]
            constructor
            · intro h; exact absurd h (by decide)
            · intro h; exact absurd h.symm (embZero_ne_embPair D hD (P.mem_X b) _ _)
        · -- j = 2b+2 (node ∩ node : recurse)
          have hlt1 : Nat.pair a.unpair.1 b.unpair.1 < Nat.pair (2 * a + 2) (2 * b + 2) :=
            pair_lt_pair_of_lt (by have := unpair_fst_le a; omega) (by have := unpair_fst_le b; omega)
          have hlt2 : Nat.pair a.unpair.2 b.unpair.2 < Nat.pair (2 * a + 2) (2 * b + 2) :=
            pair_lt_pair_of_lt (by have := unpair_snd_le a; omega) (by have := unpair_snd_le b; omega)
          have hr1 := listGet_rtbl (dsharpStep fcons feq finter) hlt1
          have hr2 := listGet_rtbl (dsharpStep fcons feq finter) hlt2
          obtain ⟨ihc1, ihi1, ihe1⟩ :=
            ih (Nat.pair a.unpair.1 b.unpair.1) (hw ▸ hlt1) a.unpair.1 b.unpair.1 rfl
          obtain ⟨ihc2, ihi2, ihe2⟩ :=
            ih (Nat.pair a.unpair.2 b.unpair.2) (hw ▸ hlt2) a.unpair.2 b.unpair.2 rfl
          simp only [gOf_def]
          rw [dsharpStep_nn fcons feq finter a b]
          simp only [eqB_packT, consB_packT, intI_packT]
          rw [hr1, hr2]
          refine ⟨?_, ?_, ?_⟩
          · rw [Vsharp_even_inter_even P, exists_sub_embPair_iff P hD, nat_mul_eq_one]
            exact and_congr ihc1 ihc2
          · intro hp
            rw [Vsharp_even_inter_even P] at hp ⊢
            rw [exists_sub_embPair_iff P hD] at hp
            obtain ⟨hp1, hp2⟩ := hp
            rw [Vsharp_even P]
            simp only [unpair_pair_fst, unpair_pair_snd]
            rw [ihi1 hp1, ihi2 hp2]
          · rw [Vsharp_even P, Vsharp_even P, nat_mul_eq_one, ihe1, ihe2]
            constructor
            · rintro ⟨h1, h2⟩; rw [h1, h2]
            · intro h; exact embPair_injective h
  intro i j
  exact key (Nat.pair i j) i j rfl

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

/-- **Intersection-index correctness in isolation.** The `intI` component of `gOf (dsharpStep …)` is
independent of the `eq`/`cons` bits (`fcons`/`feq`), so it is correct assuming only that `finter`
correctly intersects in `D`. This lets the `inter` *data* field be built with dummy `fcons`/`feq`
while staying choice-free. -/
theorem dsharp_intI_correct (hD : ∀ X, D.mem X → X.Nonempty)
    (hinter : ∀ a b, (∃ l, P.X l ⊆ P.X a ∩ P.X b) → P.X (finter (Nat.pair a b)) = P.X a ∩ P.X b) :
    ∀ i j : ℕ, (∃ l, Vsharp D P l ⊆ Vsharp D P i ∩ Vsharp D P j) →
      Vsharp D P (intI (gOf (dsharpStep fcons feq finter) (Nat.pair i j)))
        = Vsharp D P i ∩ Vsharp D P j := by
  have key : ∀ w : ℕ, ∀ i j : ℕ, Nat.pair i j = w →
      (∃ l, Vsharp D P l ⊆ Vsharp D P i ∩ Vsharp D P j) →
      Vsharp D P (intI (gOf (dsharpStep fcons feq finter) (Nat.pair i j)))
        = Vsharp D P i ∩ Vsharp D P j := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro i j hw
      rcases nat_shape i with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
      · intro _
        simp only [gOf_def]; rw [dsharpStep_i0 fcons feq finter j]
        simp only [intI_packT]; rw [Vsharp_zero_inter P]
      · rcases nat_shape j with rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
        · intro _
          simp only [gOf_def]; rw [dsharpStep_j0 fcons feq finter _ (by omega : 2 * a + 1 ≠ 0)]
          simp only [intI_packT]; exact (Vsharp_inter_zero P (2 * a + 1)).symm
        · intro hp
          simp only [gOf_def]; rw [dsharpStep_ll fcons feq finter a b]
          simp only [intI_packT]
          rw [Vsharp_odd_inter_odd P] at hp ⊢
          rw [exists_sub_embZero_iff P hD] at hp
          rw [Vsharp_odd P, hinter a b hp]
        · intro hp
          exfalso
          rw [Vsharp_odd_inter_even P] at hp
          obtain ⟨l, hl⟩ := hp
          obtain ⟨x, hx⟩ := Vsharp_nonempty P hD l
          exact absurd (hl hx) (by simp)
      · rcases nat_shape j with rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
        · intro _
          simp only [gOf_def]; rw [dsharpStep_j0 fcons feq finter _ (by omega : 2 * a + 2 ≠ 0)]
          simp only [intI_packT]; exact (Vsharp_inter_zero P (2 * a + 2)).symm
        · intro hp
          exfalso
          rw [Vsharp_even_inter_odd P] at hp
          obtain ⟨l, hl⟩ := hp
          obtain ⟨x, hx⟩ := Vsharp_nonempty P hD l
          exact absurd (hl hx) (by simp)
        · intro hp
          have hlt1 : Nat.pair a.unpair.1 b.unpair.1 < Nat.pair (2 * a + 2) (2 * b + 2) :=
            pair_lt_pair_of_lt (by have := unpair_fst_le a; omega) (by have := unpair_fst_le b; omega)
          have hlt2 : Nat.pair a.unpair.2 b.unpair.2 < Nat.pair (2 * a + 2) (2 * b + 2) :=
            pair_lt_pair_of_lt (by have := unpair_snd_le a; omega) (by have := unpair_snd_le b; omega)
          have hr1 := listGet_rtbl (dsharpStep fcons feq finter) hlt1
          have hr2 := listGet_rtbl (dsharpStep fcons feq finter) hlt2
          rw [Vsharp_even_inter_even P] at hp ⊢
          rw [exists_sub_embPair_iff P hD] at hp
          obtain ⟨hp1, hp2⟩ := hp
          simp only [gOf_def]; rw [dsharpStep_nn fcons feq finter a b]
          simp only [intI_packT]; rw [hr1, hr2, Vsharp_even P]
          simp only [unpair_pair_fst, unpair_pair_snd]
          rw [ih _ (hw ▸ hlt1) a.unpair.1 b.unpair.1 rfl hp1,
              ih _ (hw ▸ hlt2) a.unpair.2 b.unpair.2 rfl hp2]
  intro i j; exact key (Nat.pair i j) i j rfl

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

/-- **Decidability of `7.1(i)` for `D^§`.** `Vₙ ∩ Vₘ = V_k` iff `(n,m)` is consistent and the
computed intersection index agrees with `k` under `D^§`-equality. Inconsistency forces the product
to `0` (and then `Vₙ ∩ Vₘ = ∅ ≠ V_k`, since `V_k` is nonempty), so the single product decider is
correct on the nose. -/
theorem dsharp_interEq_iff (hD : ∀ X, D.mem X → X.Nonempty)
    (hcons : ∀ a b, fcons (Nat.pair a b) = 1 ↔ ∃ l, P.X l ⊆ P.X a ∩ P.X b)
    (heq : ∀ a b, feq (Nat.pair a b) = 1 ↔ P.X a = P.X b)
    (hinter : ∀ a b, (∃ l, P.X l ⊆ P.X a ∩ P.X b) → P.X (finter (Nat.pair a b)) = P.X a ∩ P.X b)
    (n m k : ℕ) :
    (Vsharp D P n ∩ Vsharp D P m = Vsharp D P k) ↔
      consB (gOf (dsharpStep fcons feq finter) (Nat.pair n m))
        * eqB (gOf (dsharpStep fcons feq finter)
            (Nat.pair (intI (gOf (dsharpStep fcons feq finter) (Nat.pair n m))) k)) = 1 := by
  obtain ⟨hc0, hi0, _⟩ := dsharp_decider_spec P fcons feq finter hD hcons heq hinter n m
  obtain ⟨_, _, he⟩ := dsharp_decider_spec P fcons feq finter hD hcons heq hinter
    (intI (gOf (dsharpStep fcons feq finter) (Nat.pair n m))) k
  rw [nat_mul_eq_one]
  constructor
  · intro hEq
    have hch : ∃ l, Vsharp D P l ⊆ Vsharp D P n ∩ Vsharp D P m := ⟨k, hEq.ge⟩
    exact ⟨hc0.mpr hch, he.mpr ((hi0 hch).trans hEq)⟩
  · rintro ⟨hcb, heb⟩
    rw [← hi0 (hc0.mp hcb)]; exact he.mp heb

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

variable (fcons feq finter : ℕ → ℕ)

/-- **Proposition 7.7 (Scott 1981, PRG-19).** A computable presentation of `D^§` from one of `D`. -/
def dsharpPresentation (hD : ∀ X, D.mem X → X.Nonempty) :
    ComputablePresentation (Dsharp D hD) where
  X := Vsharp D P
  mem_X := fun n => Vsharp_mem P n
  surj := fun hY => Vsharp_surj P hY
  interEq_computable := by
    obtain ⟨fc, hfc_pr, hfc⟩ := P.cons_computable
    obtain ⟨fe, hfe_pr, hfe⟩ := P.eq_computable
    have hcons : ∀ a b, fc (Nat.pair a b) = 1 ↔ ∃ l, P.X l ⊆ P.X a ∩ P.X b := fun a b => by
      have := hfc (Nat.pair a b); simp only [unpair_pair_fst, unpair_pair_snd] at this; exact this.symm
    have heq : ∀ a b, fe (Nat.pair a b) = 1 ↔ P.X a = P.X b := fun a b => by
      have := hfe (Nat.pair a b); simp only [unpair_pair_fst, unpair_pair_snd] at this; exact this.symm
    have hinter : ∀ a b, (∃ l, P.X l ⊆ P.X a ∩ P.X b) →
        P.X ((fun s => P.inter s.unpair.1 s.unpair.2) (Nat.pair a b)) = P.X a ∩ P.X b := fun a b h => by
      simp only [unpair_pair_fst, unpair_pair_snd]; exact P.inter_spec h
    refine ⟨fun t => consB (gOf (dsharpStep fc fe (fun s => P.inter s.unpair.1 s.unpair.2))
        (Nat.pair t.unpair.1 t.unpair.2.unpair.1))
        * eqB (gOf (dsharpStep fc fe (fun s => P.inter s.unpair.1 s.unpair.2))
            (Nat.pair (intI (gOf (dsharpStep fc fe (fun s => P.inter s.unpair.1 s.unpair.2))
              (Nat.pair t.unpair.1 t.unpair.2.unpair.1))) t.unpair.2.unpair.2)), ?_, fun t => ?_⟩
    · have hg := primrec_gOf (primrec_dsharpStep fc fe (fun s => P.inter s.unpair.1 s.unpair.2)
        hfc_pr hfe_pr P.inter_primrec)
      have hc0 := hg.comp (Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right))
      exact primrec_mul₂ ((Nat.Primrec.left.comp Nat.Primrec.right).comp hc0)
        (Nat.Primrec.left.comp (hg.comp
          (((Nat.Primrec.right.comp Nat.Primrec.right).comp hc0).pair
            (Nat.Primrec.right.comp Nat.Primrec.right))))
    · exact dsharp_interEq_iff P fc fe (fun s => P.inter s.unpair.1 s.unpair.2) hD hcons heq hinter
        t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2
  cons_computable := by
    obtain ⟨fc, hfc_pr, hfc⟩ := P.cons_computable
    obtain ⟨fe, hfe_pr, hfe⟩ := P.eq_computable
    have hcons : ∀ a b, fc (Nat.pair a b) = 1 ↔ ∃ l, P.X l ⊆ P.X a ∩ P.X b := fun a b => by
      have := hfc (Nat.pair a b); simp only [unpair_pair_fst, unpair_pair_snd] at this; exact this.symm
    have heq : ∀ a b, fe (Nat.pair a b) = 1 ↔ P.X a = P.X b := fun a b => by
      have := hfe (Nat.pair a b); simp only [unpair_pair_fst, unpair_pair_snd] at this; exact this.symm
    have hinter : ∀ a b, (∃ l, P.X l ⊆ P.X a ∩ P.X b) →
        P.X ((fun s => P.inter s.unpair.1 s.unpair.2) (Nat.pair a b)) = P.X a ∩ P.X b := fun a b h => by
      simp only [unpair_pair_fst, unpair_pair_snd]; exact P.inter_spec h
    refine ⟨fun t => consB (gOf (dsharpStep fc fe (fun s => P.inter s.unpair.1 s.unpair.2))
        (Nat.pair t.unpair.1 t.unpair.2)), ?_, fun t => ?_⟩
    · have hg := primrec_gOf (primrec_dsharpStep fc fe (fun s => P.inter s.unpair.1 s.unpair.2)
        hfc_pr hfe_pr P.inter_primrec)
      exact (Nat.Primrec.left.comp Nat.Primrec.right).comp
        (hg.comp (Nat.Primrec.left.pair Nat.Primrec.right))
    · exact (dsharp_decider_spec P fc fe (fun s => P.inter s.unpair.1 s.unpair.2) hD hcons heq hinter
        t.unpair.1 t.unpair.2).1.symm
  inter := fun n m => intI (gOf (dsharpStep (fun _ => 0) (fun _ => 0)
    (fun s => P.inter s.unpair.1 s.unpair.2)) (Nat.pair n m))
  inter_primrec := by
    have hg := primrec_gOf (primrec_dsharpStep (fun _ => 0) (fun _ => 0)
      (fun s => P.inter s.unpair.1 s.unpair.2) (Nat.Primrec.const 0) (Nat.Primrec.const 0)
      P.inter_primrec)
    have hpair : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 t.unpair.2) :=
      Nat.Primrec.left.pair Nat.Primrec.right
    exact (Nat.Primrec.right.comp Nat.Primrec.right).comp (hg.comp hpair)
  inter_spec := by
    intro n m h
    exact dsharp_intI_correct P (fun _ => 0) (fun _ => 0) (fun s => P.inter s.unpair.1 s.unpair.2) hD
      (fun a b hh => by simp only [unpair_pair_fst, unpair_pair_snd]; exact P.inter_spec hh) n m h
  masterIdx := 0
  masterIdx_spec := Vsharp_zero P

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive Example61
variable {α : Type*}

namespace Proposition77


variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)


variable (fcons feq finter : ℕ → ℕ)


/-- **Proposition 7.7 (Scott 1981, PRG-19).** If `D` is effectively given, so is `D^§`. -/
theorem dsharp_isEffectivelyGiven (P : ComputablePresentation D)
    (hD : ∀ X, D.mem X → X.Nonempty) :
    (Dsharp D hD).IsEffectivelyGiven :=
  ⟨dsharpPresentation P hD⟩

end Proposition77
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Proposition77
section
set_option linter.unusedVariables false

theorem theorem_77.{u_1} : ∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D)
  (hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X),
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Prod (List Bool) α)
    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD) :=
  @DomainTheory.NeighbourhoodSystems.Proposition77.dsharp_isEffectivelyGiven
end

end DomainTheory.NeighbourhoodSystems.Proposition77
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive Example61

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

@[simp] theorem dsharpPresentation_X (P : ComputablePresentation D) (n : ℕ) :
    (dsharpPresentation P hD).X n = Vsharp D P n := rfl

end Proposition77
end

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

/-- **Example 6.1's injection `λx. x^§` as an approximable map.** Scott's neighbourhood relation
`X (λx.x^§) W ↔ 0·X ⊆ W` (`embZero X ⊆ W`). The filter laws are immediate: `inter_right` uses
`memS_inter` (with witness `0·X`), and `mono` uses monotonicity of `embZero`. -/
def inSharpMap : ApproximableMap D (Dsharp D hD) where
  rel X W := D.mem X ∧ MemS D W ∧ embZero X ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨D.master_mem, MemS.gamma, embZero_subset_Gamma D.master_mem⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨-, hW', hsub'⟩
    exact ⟨hX, memS_inter hD hW hW' (MemS.zero hX) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' W W' ⟨hX, hW, hsub⟩ hX'X hWW' hX'mem hW'mem
    exact ⟨hX'mem, hW'mem, (embZero_subset.mpr hX'X).trans (hsub.trans hWW')⟩

end Proposition77
end

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

@[simp] theorem inSharpMap_rel {X : Set α} {W : Set (List Bool × α)} :
    (inSharpMap hD).rel X W ↔ D.mem X ∧ MemS D W ∧ embZero X ⊆ W := Iff.rfl

end Proposition77
end

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

/-- **The first projection of the pair part of `D^§`, as an approximable map.** On the pair summand
`1·P ∪ 2·Q` it returns `P`; everywhere else it returns `⊥ = {Γ}`. The neighbourhood relation is
`W proj₀ Z ↔ Z = Γ ∨ ∃ P Q, W = 1·P ∪ 2·Q ∧ P ⊆ Z`. -/
def proj0Map : ApproximableMap (Dsharp D hD) (Dsharp D hD) where
  rel W Z := MemS D W ∧ MemS D Z ∧ (Z = Gamma D ∨ ∃ Pp Qq, W = embPair Pp Qq ∧ Pp ⊆ Z)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨MemS.gamma, MemS.gamma, Or.inl rfl⟩
  inter_right := by
    rintro W Z Z' ⟨hW, hZ, hd⟩ ⟨-, hZ', hd'⟩
    have hgZ : Z ⊆ Gamma D := memS_subset_gamma hZ
    have hgZ' : Z' ⊆ Gamma D := memS_subset_gamma hZ'
    rcases hd with rfl | ⟨Pp, Qq, hWeq, hPZ⟩
    · rw [Set.inter_eq_right.mpr hgZ']; exact ⟨hW, hZ', hd'⟩
    · rcases hd' with rfl | ⟨Pp', Qq', hWeq', hPZ'⟩
      · rw [Set.inter_eq_left.mpr hgZ]; exact ⟨hW, hZ, Or.inr ⟨Pp, Qq, hWeq, hPZ⟩⟩
      · have hPP : Pp = Pp' := (embPair_injective (hWeq.symm.trans hWeq')).1
        have hPsub : Pp ⊆ Z ∩ Z' := Set.subset_inter hPZ (by rw [hPP]; exact hPZ')
        have hMemP : MemS D Pp := (memS_embPair_inv hD (hWeq ▸ hW)).1
        exact ⟨hW, memS_inter hD hZ hZ' hMemP hPsub, Or.inr ⟨Pp, Qq, hWeq, hPsub⟩⟩
  mono := by
    rintro W W' Z Z' ⟨hW, hZ, hd⟩ hW'W hZZ' hW'mem hZ'mem
    refine ⟨hW'mem, hZ'mem, ?_⟩
    rcases hd with rfl | ⟨Pp, Qq, hWeq, hPZ⟩
    · exact Or.inl (Set.Subset.antisymm (memS_subset_gamma hZ'mem) hZZ')
    · subst hWeq
      cases hW'mem with
      | gamma =>
        exact absurd (Set.Subset.antisymm (memS_subset_gamma hW) hW'W)
          (embPair_ne_Gamma D hD Pp Qq)
      | @zero X hX =>
        exfalso
        obtain ⟨a, ha⟩ := hD X hX
        rcases hW'W (show (([], a) : List Bool × α) ∈ embZero X from ⟨rfl, ha⟩) with
          ⟨p', hp', -⟩ | ⟨q', hq', -⟩
        · simp at hp'
        · simp at hq'
      | @pair Pp' Qq' hP' hQ' =>
        obtain ⟨hP'P, -⟩ := embPair_subset.mp hW'W
        exact Or.inr ⟨Pp', Qq', rfl, fun z hz => hZZ' (hPZ (hP'P hz))⟩

end Proposition77
end

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


@[simp] theorem proj0Map_rel {W Z : Set (List Bool × α)} :
    (proj0Map hD).rel W Z ↔
      MemS D W ∧ MemS D Z ∧ (Z = Gamma D ∨ ∃ Pp Qq, W = embPair Pp Qq ∧ Pp ⊆ Z) := Iff.rfl
end Proposition77
end

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


/-- **`inSharpMap` really computes `inSharp`.** Its elementwise action is Scott's `λx. x^§`. -/
theorem inSharpMap_toElementMap (x : D.Element) :
    (inSharpMap hD).toElementMap x = inSharp D hD x := by
  apply Element.ext
  intro W
  simp only [ApproximableMap.mem_toElementMap, inSharpMap_rel]
  constructor
  · rintro ⟨X, hXx, hX, hW, hsub⟩
    cases hW with
    | gamma => exact Or.inl rfl
    | @zero Y hY => exact Or.inr ⟨Y, x.up_mem hXx hY (embZero_subset.mp hsub), rfl⟩
    | @pair Pp Qq hP hQ =>
      exfalso
      obtain ⟨a, ha⟩ := hD X hX
      rcases hsub (show (([], a) : List Bool × α) ∈ embZero X from ⟨rfl, ha⟩) with
        ⟨p', hp', -⟩ | ⟨q', hq', -⟩
      · simp at hp'
      · simp at hq'
  · rintro (rfl | ⟨Y, hYx, rfl⟩)
    · exact ⟨D.master, x.master_mem, D.master_mem, MemS.gamma, embZero_subset_Gamma D.master_mem⟩
    · exact ⟨Y, hYx, x.sub hYx, MemS.zero (x.sub hYx), subset_rfl⟩

end Proposition77
end

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


/-- **Proposition 7.7 (Scott 1981, PRG-19) — `λx. x^§` is computable.**
`Xₙ (λx.x^§) V_k ↔ V_{2n+1} ⊆ V_k` (`embZero Xₙ ⊆ V_k`), a recursive slice of the inclusion
decider for `D^§`, hence r.e. -/
theorem inSharp_isComputable (P : ComputablePresentation D) :
    ComputableMap P (dsharpPresentation P hD) (inSharpMap hD) := by
  constructor
  show REPred (fun s => (inSharpMap hD).rel (P.X s.unpair.1) (Vsharp D P s.unpair.2))
  have hincl : RecDecidable (fun s => Vsharp D P s.unpair.1 ⊆ Vsharp D P s.unpair.2) :=
    (dsharpPresentation P hD).incl_computable
  have hr : Nat.Primrec (fun t => Nat.pair (2 * t.unpair.1 + 1) t.unpair.2) :=
    (primrec_add₂ (primrec_mul₂ (Nat.Primrec.const 2) Nat.Primrec.left)
      (Nat.Primrec.const 1)).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [inSharpMap_rel, unpair_pair_fst, unpair_pair_snd, Vsharp_odd]
  exact ⟨fun h => h.2.2, fun h => ⟨P.mem_X _, Vsharp_mem P _, h⟩⟩

end Proposition77
end

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


/-- The index characterization of `proj0Map` against the `Vsharp` enumeration. `V_m proj₀ V_k` iff
`k = 0` (`V_k = Γ`) or `m` is an even node index `2a+2` with `V_{p a} ⊆ V_k` (the left child). -/
theorem proj0_rel_Vsharp_iff (P : ComputablePresentation D) (m k : ℕ) :
    (proj0Map hD).rel (Vsharp D P m) (Vsharp D P k) ↔
      k = 0 ∨ (m % 2 = 0 ∧ m ≠ 0 ∧ Vsharp D P (m / 2 - 1).unpair.1 ⊆ Vsharp D P k) := by
  rw [proj0Map_rel, and_iff_right (Vsharp_mem P m), and_iff_right (Vsharp_mem P k)]
  refine or_congr (Vsharp_eq_Gamma_iff P hD k) ?_
  rcases nat_shape m with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [Vsharp_zero]
    constructor
    · rintro ⟨Pp, Qq, heq, -⟩; exact absurd heq.symm (embPair_ne_Gamma D hD Pp Qq)
    · rintro ⟨-, hne, -⟩; exact absurd rfl hne
  · rw [Vsharp_odd]
    constructor
    · rintro ⟨Pp, Qq, heq, -⟩; exact absurd heq (embZero_ne_embPair D hD (P.mem_X a) Pp Qq)
    · rintro ⟨hmod, -, -⟩; exact absurd hmod (by omega)
  · rw [Vsharp_even, show (2 * a + 2) / 2 - 1 = a from by omega]
    constructor
    · rintro ⟨Pp, Qq, heq, hPk⟩
      obtain ⟨hP, -⟩ := embPair_injective heq
      exact ⟨by omega, by omega, by rw [hP]; exact hPk⟩
    · rintro ⟨-, -, hsub⟩
      exact ⟨Vsharp D P a.unpair.1, Vsharp D P a.unpair.2, rfl, hsub⟩

end Proposition77
end

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


/-- **Proposition 7.7 (Scott 1981, PRG-19) — `proj₀` is computable.**
`V_m proj₀ V_k ↔ k = 0 ∨ (m even, m ≠ 0, V_{p(m/2-1)} ⊆ V_k)`: a disjunction of the equality and
inclusion deciders with primitive-recursive parity/child reindexings, hence r.e. -/
theorem proj0_isComputable (P : ComputablePresentation D) :
    ComputableMap (dsharpPresentation P hD) (dsharpPresentation P hD) (proj0Map hD) := by
  constructor
  show REPred (fun s => (proj0Map hD).rel (Vsharp D P s.unpair.1) (Vsharp D P s.unpair.2))
  have hk0 : RecDecidable (fun s => s.unpair.2 = 0) :=
    RecDecidable.natEq Nat.Primrec.right (Nat.Primrec.const 0)
  have hmod : RecDecidable (fun s => s.unpair.1 % 2 = 0) :=
    RecDecidable.natEq (primrec_mod2.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have hne : RecDecidable (fun s => s.unpair.1 ≠ 0) :=
    (RecDecidable.natEq Nat.Primrec.left (Nat.Primrec.const 0)).not
  have hg : Nat.Primrec (fun s => Nat.pair (s.unpair.1 / 2 - 1).unpair.1 s.unpair.2) :=
    (Nat.Primrec.left.comp (primrec_sub₂ (primrec_div2.comp Nat.Primrec.left)
      (Nat.Primrec.const 1))).pair Nat.Primrec.right
  have hincl : RecDecidable (fun s => Vsharp D P (s.unpair.1 / 2 - 1).unpair.1 ⊆
      Vsharp D P s.unpair.2) := by
    refine RecDecidable.of_iff (fun s => ?_) ((dsharpPresentation P hD).incl_computable.comp hg)
    simp only [dsharpPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact (RecDecidable.of_iff (fun s => proj0_rel_Vsharp_iff hD P s.unpair.1 s.unpair.2)
    (hk0.or (hmod.and (hne.and hincl)))).re

end Proposition77
end

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


/-- **`proj0Map` really is the first projection of the pair part:** `proj₀(⟨x, y⟩^§) = x`. -/
theorem proj0_toElementMap_pairSharp (x y : (Dsharp D hD).Element) :
    (proj0Map hD).toElementMap (pairSharp D hD x y) = x := by
  apply Element.ext
  intro Z
  simp only [ApproximableMap.mem_toElementMap, proj0Map_rel]
  constructor
  · rintro ⟨W, hWmem, hMW, hMZ, hdisj⟩
    rcases hWmem with rfl | ⟨Pp, Qq, hxP, hyQ, rfl⟩
    · rcases hdisj with rfl | ⟨Pp', Qq', hPe, -⟩
      · exact x.master_mem
      · exact absurd hPe.symm (embPair_ne_Gamma D hD Pp' Qq')
    · rcases hdisj with rfl | ⟨Pp', Qq', hPe, hP'Z⟩
      · exact x.master_mem
      · obtain ⟨hPP, -⟩ := embPair_injective hPe
        exact x.up_mem hxP hMZ (by rw [hPP]; exact hP'Z)
  · intro hxZ
    exact ⟨embPair Z (Gamma D), Or.inr ⟨Z, Gamma D, hxZ, y.master_mem, rfl⟩,
      MemS.pair (x.sub hxZ) MemS.gamma, x.sub hxZ, Or.inr ⟨Z, Gamma D, rfl, subset_rfl⟩⟩

end Proposition77
end

section
variable {α : Type*}

namespace Proposition77


variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)


theorem gList_length (step : ℕ → ℕ) (w : ℕ) : (gList step w).length = w := by
  induction w with
  | zero => rfl
  | succ w ih => rw [gList, List.length_cons, ih]

end Proposition77
end

namespace Exercise722
open Set Domain.Recursive

section
/-- Default neighbourhood for junk / empty-syntax indices: the master `Σ = Set.univ`. -/
def SsysX_default : Set (List Bool) := Set.univ
end

end Exercise722
open NeighborhoodSystem Domain.Recursive ApproximableMap

section
variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Scott's `W_k = X⁰_{p(k)} ∪ X¹_{q(k)}` with `p = ·.unpair.1`, `q = ·.unpair.2`. -/
def prodEnum (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁) (t : ℕ) :
    Set (α ⊕ β) :=
  prodNbhd (P₀.X t.unpair.1) (P₁.X t.unpair.2)
end

section
variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

@[simp] theorem prodEnum_apply (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
    (t : ℕ) : prodEnum P₀ P₁ t = prodNbhd (P₀.X t.unpair.1) (P₁.X t.unpair.2) := rfl
end

section
variable {α β γ α' β' : Type*}

/-- The product representation is determined by its two components (the `↔` form of
`prodNbhd_injective`). -/
theorem prodNbhd_eq_iff {X X' : Set α} {Y Y' : Set β} :
    prodNbhd X Y = prodNbhd X' Y' ↔ X = X' ∧ Y = Y' :=
  ⟨prodNbhd_injective, by rintro ⟨rfl, rfl⟩; rfl⟩
end

section
variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

end
end DomainTheory.NeighbourhoodSystems
end
