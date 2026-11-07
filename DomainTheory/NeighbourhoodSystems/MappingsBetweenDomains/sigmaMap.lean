module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Truth
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.bot_le
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.sigmaBot_le_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.SigmaMap
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem BitDom

section

structure SatisfiesParityEquations (g : ApproximableMap B Truth.T) : Prop where
  one : ∀ x : B.Element, g.toElementMap (sigmaElt [true] x) = Truth.trueElt
  zeroOne : ∀ x : B.Element, g.toElementMap (sigmaElt [false, true] x) = Truth.falseElt
  zeroZero : ∀ x : B.Element, g.toElementMap (sigmaElt [false, false] x) = g.toElementMap x
end

section

/-- Approximable map that prefixes neighbourhoods by a fixed string. -/
def sigmaMap (σ : Str) : ApproximableMap B B where
  rel X Y := B.mem X ∧ B.mem Y ∧ prepend σ X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨B.master_mem, B.master_mem, Set.subset_univ _⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    have hpre : B.mem (prepend σ X) := memB_prepend σ hX
    have hsubInter : prepend σ X ⊆ Y ∩ Y' := Set.subset_inter hsub hsub'
    exact ⟨hX, B.inter_mem hY hY' hpre hsubInter, hsubInter⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hsub⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', ((prepend_mono σ hX'X).trans hsub).trans hYY'⟩
end

section

theorem key (g : ApproximableMap B Truth.T) (hg : SatisfiesParityEquations g) :
    ∀ σ : Str, g.toElementMap (sigmaElt σ B.bot) = Truth.valElt (Truth.scan σ)
  | [] => by
      rw [sigmaElt_nil]
      have h1 : g.toElementMap B.bot ≤ Truth.trueElt := by
        have hm := g.toElementMap_mono (B.bot_le (sigmaElt [true] B.bot))
        rwa [hg.one] at hm
      have h2 : g.toElementMap B.bot ≤ Truth.falseElt := by
        have hm := g.toElementMap_mono (B.bot_le (sigmaElt [false, true] B.bot))
        rwa [hg.zeroOne] at hm
      exact Truth.eq_botElt_of_le h1 h2
  | [false] => by
      have hbase : g.toElementMap B.bot = Truth.botElt := by
        have h0 := key g hg []
        rwa [sigmaElt_nil] at h0
      have hb : sigmaElt [false] B.bot ≤ sigmaElt [false, false] B.bot := by
        rw [sigmaElt_bot, sigmaElt_bot]
        exact (sigmaBot_le_iff _ _).mpr ⟨[false], rfl⟩
      have hm : g.toElementMap (sigmaElt [false] B.bot) ≤ Truth.botElt := by
        have := g.toElementMap_mono hb
        rwa [hg.zeroZero, hbase] at this
      have hm2 : Truth.botElt ≤ g.toElementMap (sigmaElt [false] B.bot) :=
        Truth.botElt_le _
      exact (le_antisymm hm hm2).trans rfl
  | (true :: t) => by
      rw [show (true :: t : Str) = [true] ++ t from rfl, sigmaElt_append, hg.one,
        Truth.scan_append_true]
      rfl
  | (false :: true :: t) => by
      rw [show (false :: true :: t : Str) = [false, true] ++ t from rfl, sigmaElt_append,
        hg.zeroOne, Truth.scan_append_falseTrue]
      rfl
  | (false :: false :: t) => by
      rw [show (false :: false :: t : Str) = [false, false] ++ t from rfl, sigmaElt_append,
        hg.zeroZero, key g hg t, Truth.scan_append_falseFalse]
end

section

theorem eq_parityMap_of_satisfies {g : ApproximableMap B Truth.T}
    (hg : SatisfiesParityEquations g) : g = Truth.parityMap := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : B.mem X
  · obtain ⟨σ, rfl⟩ := hX
    rw [g.rel_iff_mem_principal (memB_cone σ)]
    show (g.toElementMap (sigmaBot σ)).mem Y ↔ Truth.parityMap.rel (cone σ) Y
    rw [← sigmaElt_bot, key g hg σ, Truth.parityMap_rel_cone]
  · exact ⟨fun hr => absurd (g.rel_dom hr) hX,
      fun hr => absurd (Truth.parityMap.rel_dom hr) hX⟩
end

section

theorem parityMap_satisfies : SatisfiesParityEquations Truth.parityMap where
  one x := by
    apply Element.ext
    intro Y
    rw [Truth.parityMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, _, hval⟩
      rwa [Truth.scan_append_true] at hval
    · intro hval
      exact ⟨[], by rw [cone.nil]; exact x.master_mem, by rwa [Truth.scan_append_true]⟩
  zeroOne x := by
    apply Element.ext
    intro Y
    rw [Truth.parityMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, _, hval⟩
      rwa [Truth.scan_append_falseTrue] at hval
    · intro hval
      exact ⟨[], by rw [cone.nil]; exact x.master_mem, by rwa [Truth.scan_append_falseTrue]⟩
  zeroZero x := by
    apply Element.ext
    intro Y
    rw [Truth.parityMap_toElementMap_sigmaElt, Truth.parityMap_toElementMap_mem]
    constructor
    · rintro ⟨τ, hτ, hval⟩
      exact ⟨τ, hτ, by rwa [Truth.scan_append_falseFalse] at hval⟩
    · rintro ⟨τ, hτ, hval⟩
      exact ⟨τ, hτ, by rwa [Truth.scan_append_falseFalse]⟩
end

section

theorem toElementMap_sigmaMap (σ : Str) (x : B.Element) :
    (sigmaMap σ).toElementMap x = sigmaElt σ x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hxX, _, hY, hsub⟩
    exact ⟨hY, X, hxX, hsub⟩
  · rintro ⟨hY, X, hxX, hsub⟩
    exact ⟨X, hxX, x.sub hxX, hY, hsub⟩
end

end DomainTheory.NeighbourhoodSystems.SigmaMap
