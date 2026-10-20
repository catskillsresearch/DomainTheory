module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise719.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}


variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β} {U : NeighborhoodSystem γ}



/-- **Exercise 7.19 — Scott's displayed formula.** On generators (finite lists of down-sets)
`(ℙf).rel (⋃_{X∈L₁} ↓X) (⋃_{Y∈L₂} ↓Y) ↔ ∀ X ∈ L₁, ∃ Y ∈ L₂, X f Y`, exactly Scott's
`∀ i < n ∃ j < m. Xᵢ f Yⱼ`. (`→` reads off the generators `Xᵢ`; `←` extends to all members by `mono`
and downward closure of the target.) -/
theorem PFmap_rel_fin (f : ApproximableMap V W) {L₁ : List (Set α)} {L₂ : List (Set β)}
    (hL₁ : ∀ X ∈ L₁, V.mem X) (hL₂ : ∀ Y ∈ L₂, W.mem Y) :
    (PFmap f).rel (⋃ X ∈ L₁, V.upSet X) (⋃ Y ∈ L₂, W.upSet Y)
      ↔ ∀ X ∈ L₁, ∃ Y ∈ L₂, f.rel X Y := by
  constructor
  · rintro ⟨-, -, hbody⟩ X hX
    have hXin : X ∈ ⋃ X' ∈ L₁, V.upSet X' :=
      (V.mem_PDunion).mpr ⟨X, hX, hL₁ X hX, subset_rfl⟩
    obtain ⟨Z, hZin, hrel⟩ := hbody X hXin
    obtain ⟨Y, hY, hZmem, hZsub⟩ := (W.mem_PDunion).mp hZin
    exact ⟨Y, hY, f.mono hrel subset_rfl hZsub (hL₁ X hX) (hL₂ Y hY)⟩
  · intro hgen
    refine ⟨⟨L₁, hL₁, rfl⟩, ⟨L₂, hL₂, rfl⟩, ?_⟩
    rintro Z hZin
    obtain ⟨X, hX, hZmem, hZsub⟩ := (V.mem_PDunion).mp hZin
    obtain ⟨Y, hY, hrel⟩ := hgen X hX
    exact ⟨Y, (W.mem_PDunion).mpr ⟨Y, hY, hL₂ Y hY, subset_rfl⟩,
      f.mono hrel hZsub subset_rfl hZmem (hL₂ Y hY)⟩

end DomainTheory.NeighbourhoodSystems
