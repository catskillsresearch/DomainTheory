module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419


variable {β : Type*}


theorem prod_principal_pair (b₀ : Bool) (σ : Str) (b₁ : Bool) (τ : Str) :
    (prod C C).principal (prod_mem_prodNbhd (memC_shape b₀ σ) (memC_shape b₁ τ))
      = pair (shapeElem b₀ σ) (shapeElem b₁ τ) := by
  apply Element.ext
  intro P
  rw [mem_principal]
  constructor
  · rintro ⟨hP, hsub⟩
    obtain ⟨X', Y', hX', hY', rfl⟩ := hP
    obtain ⟨hsX, hsY⟩ := prodNbhd_subset_iff.mp hsub
    exact ⟨X', Y', ⟨hX', hsX⟩, ⟨hY', hsY⟩, rfl⟩
  · rintro ⟨X', Y', ⟨hX', hsX⟩, ⟨hY', hsY⟩, rfl⟩
    exact ⟨prod_mem_prodNbhd hX' hY', prodNbhd_subset_iff.mpr ⟨hsX, hsY⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise516
