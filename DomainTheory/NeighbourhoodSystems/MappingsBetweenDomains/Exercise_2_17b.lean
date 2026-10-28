module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example_2_4

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_22
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_20
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_8
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example24
open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

section

theorem eq_runMap_of_satisfies {g : ApproximableMap B B} (hg : SatisfiesRunEquations g) :
    g = runMap := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : B.mem X
  · obtain ⟨σ, rfl⟩ := hX
    rw [g.rel_iff_mem_principal (memB_cone σ)]
    show (g.toElementMap (sigmaBot σ)).mem Y ↔ runMap.rel (cone σ) Y
    rw [← sigmaElt_bot, key g hg σ, sigmaElt_bot, runMap_rel_cone]
    show (B.principal (memB_cone (out σ))).mem Y ↔ B.mem Y ∧ cone (out σ) ⊆ Y
    exact B.mem_principal (memB_cone (out σ))
  · exact ⟨fun hr => absurd (g.rel_dom hr) hX, fun hr => absurd (runMap.rel_dom hr) hX⟩
end

section

theorem runMap_toElementMap_mem (x : B.Element) (Y : Set Str) :
    (runMap.toElementMap x).mem Y ↔ ∃ τ, x.mem (cone τ) ∧ B.mem Y ∧ cone (out τ) ⊆ Y := by
  constructor
  · rintro ⟨X, hX, hrel⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    exact ⟨τ, hX, (runMap_rel_cone τ Y).mp hrel⟩
  · rintro ⟨τ, hτ, hYmem, hsub⟩
    exact ⟨cone τ, hτ, (runMap_rel_cone τ Y).mpr ⟨hYmem, hsub⟩⟩
end

section

theorem runMap_toElementMap_sigmaElt (σ : Str) (x : B.Element) (Y : Set Str) :
    (runMap.toElementMap (sigmaElt σ x)).mem Y ↔
      ∃ τ, x.mem (cone τ) ∧ B.mem Y ∧ cone (out (σ ++ τ)) ⊆ Y := by
  constructor
  · rintro ⟨Z, ⟨_, X, hX, hsub⟩, ρ, rfl, hYmem, hsubOut⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    rw [prepend_cone] at hsub
    exact ⟨τ, hX, hYmem, (cone_subset_cone.mpr (out_mono (cone_subset_cone.mp hsub))).trans hsubOut⟩
  · rintro ⟨τ, hτ, hYmem, hsub⟩
    exact ⟨cone (σ ++ τ), ⟨memB_cone _, cone τ, hτ, (prepend_cone σ τ).le⟩,
      (runMap_rel_cone (σ ++ τ) Y).mpr ⟨hYmem, hsub⟩⟩
end

section

theorem sigmaElt_runMap_toElementMap (τ₀ : Str) (x : B.Element) (Y : Set Str) :
    (sigmaElt τ₀ (runMap.toElementMap x)).mem Y ↔
      ∃ τ, x.mem (cone τ) ∧ B.mem Y ∧ cone (τ₀ ++ out τ) ⊆ Y := by
  constructor
  · rintro ⟨hYmem, Z, hZ, hsub⟩
    obtain ⟨τ, hτ, _, hZsub⟩ := (runMap_toElementMap_mem x Z).mp hZ
    refine ⟨τ, hτ, hYmem, ?_⟩
    rw [← prepend_cone]
    exact (prepend_mono τ₀ hZsub).trans hsub
  · rintro ⟨τ, hτ, hYmem, hsub⟩
    refine ⟨hYmem, cone (out τ),
      (runMap_toElementMap_mem x _).mpr ⟨τ, hτ, memB_cone _, subset_rfl⟩, ?_⟩
    rw [prepend_cone]
    exact hsub
end

section

theorem runMap_satisfies : SatisfiesRunEquations runMap where
  zero x := by
    apply Element.ext
    intro Y
    rw [runMap_toElementMap_sigmaElt, sigmaElt_runMap_toElementMap]
    constructor
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      exact ⟨τ, hτ, hYmem, by rwa [out_append_false] at hsub⟩
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      exact ⟨τ, hτ, hYmem, by rwa [out_append_false]⟩
  oneOne x := by
    apply Element.ext
    intro Y
    rw [runMap_toElementMap_sigmaElt, runMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      exact ⟨τ, hτ, hYmem, by rwa [out_append_trueTrue] at hsub⟩
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      exact ⟨τ, hτ, hYmem, by rwa [← out_append_trueTrue] at hsub⟩
  oneZero x := by
    apply Element.ext
    intro Y
    rw [runMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      rw [out_append_trueFalse] at hsub
      exact ⟨hYmem, cone τ, hτ, by rw [prepend_cone]; exact hsub⟩
    · rintro ⟨hYmem, X, hX, hsub⟩
      obtain ⟨τ, rfl⟩ := x.sub hX
      rw [prepend_cone] at hsub
      exact ⟨τ, hX, hYmem, by rwa [out_append_trueFalse]⟩
  one := by
    apply Element.ext
    intro Y
    rw [runMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      obtain rfl : τ = [] := bot_mem_cone_iff.mp hτ
      rw [show out ([true] ++ ([] : Str)) = ([] : Str) from rfl, cone_nil] at hsub
      rw [mem_bot]
      exact Set.eq_univ_of_univ_subset hsub
    · intro hY
      rw [mem_bot] at hY
      refine ⟨[], bot_mem_cone_iff.mpr rfl, hY ▸ B.master_mem, ?_⟩
      rw [show out ([true] ++ ([] : Str)) = ([] : Str) from rfl, cone_nil, hY, B_master]
end

end DomainTheory.NeighbourhoodSystems.Example24

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

section
open NeighborhoodSystem
universe u
variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

instance instNonemptyMemSubtype (x : V₀.Element) : Nonempty {X : Set α // x.mem X} :=
  ⟨⟨V₀.master, x.master_mem⟩⟩

theorem continuous_monotone {c : V₀.Element → V₁.Element} (hc : Continuous c) : Monotone c := by
  intro x y hxy
  rw [V₁.le_iff_isOpen_imp]
  intro U hU hxU
  exact V₀.isOpen_isUpperSet (hU.preimage hc) hxU hxy

end

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
