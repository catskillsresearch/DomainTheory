module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.Language
import DomainTheory.DataTypesAsLattices.Closures.botElem
import DomainTheory.DataTypesAsLattices.Continuous.mem_scottUnion
import DomainTheory.DataTypesAsLattices.Lambda.ofNat_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def zeroPrime : Pomega := ofNat 0 ∪ ofNat 1

namespace zeroPrime

theorem ne_ofNat_zero : zeroPrime ≠ ofNat 0 := by
  intro h
  have : (1 : ℕ) ∈ ofNat 0 := by
    have : (1 : ℕ) ∈ zeroPrime := Or.inr rfl
    rwa [h] at this
  simp [ofNat] at this

theorem ne_top : zeroPrime ≠ topElem := by
  intro h
  have : (2 : ℕ) ∈ zeroPrime := by rw [h]; exact Set.mem_univ 2
  simp [zeroPrime, ofNat] at this

end zeroPrime

theorem zero_not_mem_succSet_top : 0 ∉ succSet topElem := by
  intro h
  obtain ⟨n, _, hn⟩ := h
  exact Nat.succ_ne_zero n hn.symm

def uvU (x y : Pomega) : Pomega :=
  {k | (k = 0 ∧ (x.Nonempty ∨ y.Nonempty)) ∨
       (k = 1 ∧ ((0 ∈ x ∧ ∃ n, n + 1 ∈ y) ∨ ((∃ n, n + 1 ∈ x) ∧ 0 ∈ y)))}

namespace uvU

theorem mono_left {x x' y : Pomega} (h : x ⊆ x') : uvU x y ⊆ uvU x' y := by
  intro k hk
  rcases hk with ⟨rfl, hne⟩ | ⟨rfl, h1⟩
  · exact Or.inl ⟨rfl, hne.imp_left fun ⟨n, hn⟩ => ⟨n, h hn⟩⟩
  · rcases h1 with h10 | ⟨⟨n, hn⟩, h0⟩
    · exact Or.inr ⟨rfl, Or.inl ⟨h h10.1, h10.2⟩⟩
    · exact Or.inr ⟨rfl, Or.inr ⟨⟨n, h hn⟩, h0⟩⟩

theorem mono_right {x y y' : Pomega} (h : y ⊆ y') : uvU x y ⊆ uvU x y' := by
  intro k hk
  rcases hk with ⟨rfl, hne⟩ | ⟨rfl, h1⟩
  · exact Or.inl ⟨rfl, hne.imp_right fun ⟨n, hn⟩ => ⟨n, h hn⟩⟩
  · rcases h1 with ⟨h0, ⟨n, hn⟩⟩ | h10
    · exact Or.inr ⟨rfl, Or.inl ⟨h0, ⟨n, h hn⟩⟩⟩
    · exact Or.inr ⟨rfl, Or.inr ⟨h10.1, h h10.2⟩⟩

theorem isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun x => uvU x y) := by
  constructor
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with ⟨rfl, hne⟩ | ⟨rfl, h1⟩
    · rcases hne with ⟨n, hn⟩ | hy
      · exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e.pow2, Set.singleton_subset_iff, hn],
          Or.inl ⟨rfl, Or.inl ⟨n, by simp [e.pow2]⟩⟩⟩
      · exact mem_scottUnion.mpr ⟨0, by simp [e.zero], Or.inl ⟨rfl, Or.inr hy⟩⟩
    · rcases h1 with ⟨h0, hp⟩ | ⟨⟨n, hn⟩, h0⟩
      · exact mem_scottUnion.mpr ⟨1, by simp [e_one, h0],
          Or.inr ⟨rfl, Or.inl ⟨by simp [e_one], hp⟩⟩⟩
      · exact mem_scottUnion.mpr ⟨2 ^ (n + 1), by simp [e.pow2, Set.singleton_subset_iff, hn],
          Or.inr ⟨rfl, Or.inr ⟨⟨n, by simp [e.pow2]⟩, h0⟩⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    exact mono_left hm hkm

theorem isScottContinuous_right (x : Pomega) :
    IsScottContinuous (fun y => uvU x y) := by
  constructor
  intro y
  ext k
  constructor
  · intro hk
    rcases hk with ⟨rfl, hne⟩ | ⟨rfl, h1⟩
    · rcases hne with hx | ⟨n, hn⟩
      · exact mem_scottUnion.mpr ⟨0, by simp [e.zero], Or.inl ⟨rfl, Or.inl hx⟩⟩
      · exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e.pow2, Set.singleton_subset_iff, hn],
          Or.inl ⟨rfl, Or.inr ⟨n, by simp [e.pow2]⟩⟩⟩
    · rcases h1 with ⟨h0, ⟨n, hn⟩⟩ | ⟨hp, h0⟩
      · exact mem_scottUnion.mpr ⟨2 ^ (n + 1), by simp [e.pow2, Set.singleton_subset_iff, hn],
          Or.inr ⟨rfl, Or.inl ⟨h0, ⟨n, by simp [e.pow2]⟩⟩⟩⟩
      · exact mem_scottUnion.mpr ⟨1, by simp [e_one, h0],
          Or.inr ⟨rfl, Or.inr ⟨hp, by simp [e_one]⟩⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    exact mono_right hm hkm

theorem bot_bot : uvU botElem botElem = botElem := by
  ext k
  simp [uvU, botElem]

theorem bot_zero : uvU botElem (ofNat 0) = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨hk1, h1⟩
    · simpa [ofNat] using hk0
    · rcases h1 with ⟨h0, _⟩ | ⟨⟨n, hn⟩, _⟩
      · exact ((mem_botElem 0).mp h0).elim
      · exact ((mem_botElem (n + 1)).mp hn).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl ⟨hk, Or.inr ofNat.zero_nonempty⟩

theorem zero_bot : uvU (ofNat 0) botElem = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨_, h1⟩
    · simpa [ofNat] using hk0
    · rcases h1 with ⟨_, ⟨n, hn⟩⟩ | ⟨⟨n, hn⟩, _⟩
      · exact ((mem_botElem (n + 1)).mp hn).elim
      · exact (ofNat.zero_not_pos ⟨n, hn⟩).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl ⟨hk, Or.inl ofNat.zero_nonempty⟩

theorem zero_zero : uvU (ofNat 0) (ofNat 0) = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨_, h1⟩
    · simpa [ofNat] using hk0
    · rcases h1 with ⟨_, hp⟩ | ⟨hp, _⟩
      · exact (ofNat.zero_not_pos hp).elim
      · exact (ofNat.zero_not_pos hp).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl ⟨hk, Or.inl ofNat.zero_nonempty⟩

theorem bot_top : uvU botElem topElem = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨_, h1⟩
    · simpa [ofNat] using hk0
    · rcases h1 with ⟨h0, _⟩ | ⟨⟨n, hn⟩, _⟩
      · exact ((mem_botElem 0).mp h0).elim
      · exact ((mem_botElem (n + 1)).mp hn).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl ⟨hk, Or.inr ⟨0, Set.mem_univ 0⟩⟩

theorem top_bot : uvU topElem botElem = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨_, h1⟩
    · simpa [ofNat] using hk0
    · rcases h1 with ⟨_, ⟨n, hn⟩⟩ | ⟨_, h0⟩
      · exact ((mem_botElem (n + 1)).mp hn).elim
      · exact ((mem_botElem 0).mp h0).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl ⟨hk, Or.inl ⟨0, Set.mem_univ 0⟩⟩

theorem zero_top : uvU (ofNat 0) topElem = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨hk1, _⟩
    · exact Or.inl hk0
    · exact Or.inr hk1
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl ⟨hk0, Or.inr ⟨0, Set.mem_univ 0⟩⟩
    · exact Or.inr ⟨hk1, Or.inl ⟨rfl, topElem.pos⟩⟩

theorem top_zero : uvU topElem (ofNat 0) = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨hk1, _⟩
    · exact Or.inl hk0
    · exact Or.inr hk1
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl ⟨hk0, Or.inl ⟨0, Set.mem_univ 0⟩⟩
    · exact Or.inr ⟨hk1, Or.inr ⟨topElem.pos, rfl⟩⟩

theorem top_top : uvU topElem topElem = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with ⟨hk0, _⟩ | ⟨hk1, _⟩
    · exact Or.inl hk0
    · exact Or.inr hk1
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl ⟨hk0, Or.inl ⟨0, Set.mem_univ 0⟩⟩
    · exact Or.inr ⟨hk1, Or.inl ⟨Set.mem_univ 0, topElem.pos⟩⟩

end uvU

def uvV (x y : Pomega) : Pomega :=
  {k | k = 0 ∨
       (k = 1 ∧ ((∃ n, n + 1 ∈ x) ∨ (∃ n, n + 1 ∈ y))) ∨
       (0 ∈ x ∧ (∃ n, n + 1 ∈ x) ∧ 0 ∈ y ∧ (∃ n, n + 1 ∈ y))}

namespace uvV

theorem mono_left {x x' y : Pomega} (h : x ⊆ x') : uvV x y ⊆ uvV x' y := by
  intro k hk
  rcases hk with hk0 | ⟨hk1, hpos⟩ | ⟨h0, ⟨n, hn⟩, h0y, hpy⟩
  · exact Or.inl hk0
  · exact Or.inr (Or.inl ⟨hk1, hpos.imp_left fun ⟨n, hn⟩ => ⟨n, h hn⟩⟩)
  · exact Or.inr (Or.inr ⟨h h0, ⟨n, h hn⟩, h0y, hpy⟩)

theorem mono_right {x y y' : Pomega} (h : y ⊆ y') : uvV x y ⊆ uvV x y' := by
  intro k hk
  rcases hk with hk0 | ⟨hk1, hpos⟩ | ⟨h0, hpx, h0y, ⟨n, hn⟩⟩
  · exact Or.inl hk0
  · exact Or.inr (Or.inl ⟨hk1, hpos.imp_right fun ⟨n, hn⟩ => ⟨n, h hn⟩⟩)
  · exact Or.inr (Or.inr ⟨h0, hpx, h h0y, ⟨n, h hn⟩⟩)

theorem isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun x => uvV x y) := by
  constructor
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨rfl, hpos⟩ | ⟨h0, ⟨n, hn⟩, h0y, hpy⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e.zero], Or.inl hk0⟩
    · rcases hpos with ⟨n, hn⟩ | hy
      · exact mem_scottUnion.mpr ⟨2 ^ (n + 1), by simp [e.pow2, Set.singleton_subset_iff, hn],
          Or.inr (Or.inl ⟨rfl, Or.inl ⟨n, by simp [e.pow2]⟩⟩)⟩
      · exact mem_scottUnion.mpr ⟨0, by simp [e.zero],
          Or.inr (Or.inl ⟨rfl, Or.inr hy⟩)⟩
    · refine mem_scottUnion.mpr ⟨1 ||| 2 ^ (n + 1), e.or_of_subset
        (by simp [e_one, Set.singleton_subset_iff, h0])
        (by simp [e.pow2, Set.singleton_subset_iff, hn]), ?_⟩
      refine Or.inr (Or.inr ⟨?_, ⟨n, ?_⟩, h0y, hpy⟩)
      · simp [e.or, e_one]
      · simp [e.or, e.pow2]
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    exact mono_left hm hkm

theorem isScottContinuous_right (x : Pomega) :
    IsScottContinuous (fun y => uvV x y) := by
  constructor
  intro y
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨rfl, hpos⟩ | ⟨h0, hpx, h0y, ⟨n, hn⟩⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e.zero], Or.inl hk0⟩
    · rcases hpos with hx | ⟨n, hn⟩
      · exact mem_scottUnion.mpr ⟨0, by simp [e.zero],
          Or.inr (Or.inl ⟨rfl, Or.inl hx⟩)⟩
      · exact mem_scottUnion.mpr ⟨2 ^ (n + 1), by simp [e.pow2, Set.singleton_subset_iff, hn],
          Or.inr (Or.inl ⟨rfl, Or.inr ⟨n, by simp [e.pow2]⟩⟩)⟩
    · refine mem_scottUnion.mpr ⟨1 ||| 2 ^ (n + 1), e.or_of_subset
        (by simp [e_one, Set.singleton_subset_iff, h0y])
        (by simp [e.pow2, Set.singleton_subset_iff, hn]), ?_⟩
      refine Or.inr (Or.inr ⟨h0, hpx, ?_, ⟨n, ?_⟩⟩)
      · simp [e.or, e_one]
      · simp [e.or, e.pow2]
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    exact mono_right hm hkm

theorem bot_bot : uvV botElem botElem = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨hk1, hpos⟩ | htop
    · simpa [ofNat] using hk0
    · rcases hpos with ⟨n, hn⟩ | ⟨n, hn⟩ <;> exact ((mem_botElem (n + 1)).mp hn).elim
    · exact ((mem_botElem 0).mp htop.1).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl hk

theorem bot_zero : uvV botElem (ofNat 0) = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨hk1, hpos⟩ | htop
    · simpa [ofNat] using hk0
    · rcases hpos with ⟨n, hn⟩ | hp
      · exact ((mem_botElem (n + 1)).mp hn).elim
      · exact (ofNat.zero_not_pos hp).elim
    · exact ((mem_botElem 0).mp htop.1).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl hk

theorem zero_bot : uvV (ofNat 0) botElem = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨_, hpos⟩ | htop
    · simpa [ofNat] using hk0
    · rcases hpos with hp | ⟨n, hn⟩
      · exact (ofNat.zero_not_pos hp).elim
      · exact ((mem_botElem (n + 1)).mp hn).elim
    · exact ((mem_botElem 0).mp htop.2.2.1).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl hk

theorem zero_zero : uvV (ofNat 0) (ofNat 0) = ofNat 0 := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨_, hpos⟩ | htop
    · simpa [ofNat] using hk0
    · rcases hpos with hp | hp
      · exact (ofNat.zero_not_pos hp).elim
      · exact (ofNat.zero_not_pos hp).elim
    · exact (ofNat.zero_not_pos htop.2.1).elim
  · intro hk
    simp [ofNat] at hk
    exact Or.inl hk

theorem bot_top : uvV botElem topElem = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨hk1, _⟩ | htop
    · exact Or.inl hk0
    · exact Or.inr hk1
    · exact ((mem_botElem 0).mp htop.1).elim
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl hk0
    · exact Or.inr (Or.inl ⟨hk1, Or.inr topElem.pos⟩)

theorem top_bot : uvV topElem botElem = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨hk1, _⟩ | htop
    · exact Or.inl hk0
    · exact Or.inr hk1
    · exact ((mem_botElem 0).mp htop.2.2.1).elim
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl hk0
    · exact Or.inr (Or.inl ⟨hk1, Or.inl topElem.pos⟩)

theorem zero_top : uvV (ofNat 0) topElem = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨hk1, _⟩ | htop
    · exact Or.inl hk0
    · exact Or.inr hk1
    · exact (ofNat.zero_not_pos htop.2.1).elim
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl hk0
    · exact Or.inr (Or.inl ⟨hk1, Or.inr topElem.pos⟩)

theorem top_zero : uvV topElem (ofNat 0) = zeroPrime := by
  ext k
  constructor
  · intro hk
    rcases hk with hk0 | ⟨hk1, _⟩ | htop
    · exact Or.inl hk0
    · exact Or.inr hk1
    · exact (ofNat.zero_not_pos htop.2.2.2).elim
  · intro hk
    rcases hk with hk0 | hk1
    · exact Or.inl hk0
    · exact Or.inr (Or.inl ⟨hk1, Or.inl topElem.pos⟩)

theorem top_top : uvV topElem topElem = topElem := by
  ext k
  constructor
  · intro _; exact Set.mem_univ k
  · intro _
    exact Or.inr (Or.inr ⟨Set.mem_univ 0, topElem.pos, Set.mem_univ 0, topElem.pos⟩)

end uvV

class ThreeValued (x : Pomega) : Prop where
  out : x = botElem ∨ x = ofNat 0 ∨ x = topElem

namespace ThreeValued

theorem uvU_eq_uvV {x y : Pomega} (hx : ThreeValued x) (hy : ThreeValued y) :
    uvU x y = uvV x y ↔ x = ofNat 0 ∨ y = ofNat 0 := by
  rcases hx.out with rfl | rfl | rfl <;> rcases hy.out with rfl | rfl | rfl
  · simp [uvU.bot_bot, uvV.bot_bot, botElem.ne_ofNat_zero]
  · simp [uvU.bot_zero, uvV.bot_zero]
  · constructor
    · intro h
      rw [uvU.bot_top, uvV.bot_top] at h
      exact (zeroPrime.ne_ofNat_zero h.symm).elim
    · intro h
      rcases h with h | h
      · exact (botElem.ne_ofNat_zero h).elim
      · exact (topElem.ne_ofNat_zero h).elim
  · simp [uvU.zero_bot, uvV.zero_bot]
  · simp [uvU.zero_zero, uvV.zero_zero]
  · simp [uvU.zero_top, uvV.zero_top]
  · constructor
    · intro h
      rw [uvU.top_bot, uvV.top_bot] at h
      exact (zeroPrime.ne_ofNat_zero h.symm).elim
    · intro h
      rcases h with h | h
      · exact (topElem.ne_ofNat_zero h).elim
      · exact (botElem.ne_ofNat_zero h).elim
  · simp [uvU.top_zero, uvV.top_zero]
  · constructor
    · intro h
      rw [uvU.top_top, uvV.top_top] at h
      exact (zeroPrime.ne_top h).elim
    · intro h
      rcases h with h | h <;> exact (topElem.ne_ofNat_zero h).elim

end ThreeValued

def typicalBdelta : Set Pomega :=
  {u | funOf u (ofNat 0) = funOf u (ofNat 1)}

end DomainTheory.DataTypesAsLattices
