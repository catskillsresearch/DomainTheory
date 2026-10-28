module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example_2_3
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_8
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise216
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

section

structure SatisfiesParityEquations (g : ApproximableMap B Example23.T) : Prop where
  one : ∀ x : B.Element, g.toElementMap (sigmaElt [true] x) = Example23.trueElt
  zeroOne : ∀ x : B.Element, g.toElementMap (sigmaElt [false, true] x) = Example23.falseElt
  zeroZero : ∀ x : B.Element, g.toElementMap (sigmaElt [false, false] x) = g.toElementMap x
end

section

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

theorem key (g : ApproximableMap B Example23.T) (hg : SatisfiesParityEquations g) :
    ∀ σ : Str, g.toElementMap (sigmaElt σ B.bot) = Example23.valElt (Example23.scan σ)
  | [] => by
      rw [sigmaElt_nil]
      have h1 : g.toElementMap B.bot ≤ Example23.trueElt := by
        have hm := g.toElementMap_mono (B.bot_le (sigmaElt [true] B.bot))
        rwa [hg.one] at hm
      have h2 : g.toElementMap B.bot ≤ Example23.falseElt := by
        have hm := g.toElementMap_mono (B.bot_le (sigmaElt [false, true] B.bot))
        rwa [hg.zeroOne] at hm
      exact Example23.eq_botElt_of_le h1 h2
  | [false] => by
      have hbase : g.toElementMap B.bot = Example23.botElt := by
        have h0 := key g hg []
        rwa [sigmaElt_nil] at h0
      have hb : sigmaElt [false] B.bot ≤ sigmaElt [false, false] B.bot := by
        rw [sigmaElt_bot, sigmaElt_bot]
        exact (sigmaBot_le_iff _ _).mpr ⟨[false], rfl⟩
      have hm : g.toElementMap (sigmaElt [false] B.bot) ≤ Example23.botElt := by
        have := g.toElementMap_mono hb
        rwa [hg.zeroZero, hbase] at this
      have hm2 : Example23.botElt ≤ g.toElementMap (sigmaElt [false] B.bot) :=
        Example23.botElt_le _
      exact (le_antisymm hm hm2).trans rfl
  | (true :: t) => by
      rw [show (true :: t : Str) = [true] ++ t from rfl, sigmaElt_append, hg.one,
        Example23.scan_append_true]
      rfl
  | (false :: true :: t) => by
      rw [show (false :: true :: t : Str) = [false, true] ++ t from rfl, sigmaElt_append,
        hg.zeroOne, Example23.scan_append_falseTrue]
      rfl
  | (false :: false :: t) => by
      rw [show (false :: false :: t : Str) = [false, false] ++ t from rfl, sigmaElt_append,
        hg.zeroZero, key g hg t, Example23.scan_append_falseFalse]
end

section

theorem eq_parityMap_of_satisfies {g : ApproximableMap B Example23.T}
    (hg : SatisfiesParityEquations g) : g = Example23.parityMap := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : B.mem X
  · obtain ⟨σ, rfl⟩ := hX
    rw [g.rel_iff_mem_principal (memB_cone σ)]
    show (g.toElementMap (sigmaBot σ)).mem Y ↔ Example23.parityMap.rel (cone σ) Y
    rw [← sigmaElt_bot, key g hg σ, Example23.parityMap_rel_cone]
  · exact ⟨fun hr => absurd (g.rel_dom hr) hX,
      fun hr => absurd (Example23.parityMap.rel_dom hr) hX⟩
end

section

theorem parityMap_satisfies : SatisfiesParityEquations Example23.parityMap where
  one x := by
    apply Element.ext
    intro Y
    rw [Example23.parityMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, _, hval⟩
      rwa [Example23.scan_append_true] at hval
    · intro hval
      exact ⟨[], by rw [cone_nil]; exact x.master_mem, by rwa [Example23.scan_append_true]⟩
  zeroOne x := by
    apply Element.ext
    intro Y
    rw [Example23.parityMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, _, hval⟩
      rwa [Example23.scan_append_falseTrue] at hval
    · intro hval
      exact ⟨[], by rw [cone_nil]; exact x.master_mem, by rwa [Example23.scan_append_falseTrue]⟩
  zeroZero x := by
    apply Element.ext
    intro Y
    rw [Example23.parityMap_toElementMap_sigmaElt, Example23.parityMap_toElementMap_mem]
    constructor
    · rintro ⟨τ, hτ, hval⟩
      exact ⟨τ, hτ, by rwa [Example23.scan_append_falseFalse] at hval⟩
    · rintro ⟨τ, hτ, hval⟩
      exact ⟨τ, hτ, by rwa [Example23.scan_append_falseFalse]⟩
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

section
set_option linter.unusedVariables false

theorem example_216 : And
  (∀
    {g :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.Example23.T},
    DomainTheory.NeighbourhoodSystems.Exercise216.SatisfiesParityEquations g →
      @Eq
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.ExampleB.B
          DomainTheory.NeighbourhoodSystems.Example23.T)
        g DomainTheory.NeighbourhoodSystems.Example23.parityMap)
  (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str)
    (x :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B (DomainTheory.NeighbourhoodSystems.Exercise216.sigmaMap σ) x)
      (DomainTheory.NeighbourhoodSystems.ExampleB.sigmaElt σ x)) :=
  @And.intro
  (∀
    {g :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.Example23.T},
    DomainTheory.NeighbourhoodSystems.Exercise216.SatisfiesParityEquations g →
      @Eq
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.ExampleB.B
          DomainTheory.NeighbourhoodSystems.Example23.T)
        g DomainTheory.NeighbourhoodSystems.Example23.parityMap)
  (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str)
    (x :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B (DomainTheory.NeighbourhoodSystems.Exercise216.sigmaMap σ) x)
      (DomainTheory.NeighbourhoodSystems.ExampleB.sigmaElt σ x))
  (@DomainTheory.NeighbourhoodSystems.Exercise216.eq_parityMap_of_satisfies)
  DomainTheory.NeighbourhoodSystems.Exercise216.toElementMap_sigmaMap
end

end DomainTheory.NeighbourhoodSystems.Exercise216
