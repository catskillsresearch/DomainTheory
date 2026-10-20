module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.smashFadeInner_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84b.smashRetraction_mem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}





section Smash






/-- **`smashRetraction`'s closed form.** `smash(z) = z` if neither coordinate is `⊥`; otherwise
`smash(z) = ⊥`. -/
theorem smashRetraction_mem_iff {z : (prod D E).Element} {Z : Set (α ⊕ β)} :
    (smashRetraction.toElementMap z).mem Z ↔
      (prod D E).mem Z ∧
        (Z = (prod D E).master ∨ (z.fst ≠ D.bot ∧ z.snd ≠ E.bot ∧ z.mem Z)) := by
  rw [smashRetraction_mem, smashFadeInner_mem]
  constructor
  · rintro ⟨hPZ, hZeq | ⟨hx, hPZ', hZeq' | ⟨hy, hzZ⟩⟩⟩
    · exact ⟨hPZ, Or.inl hZeq⟩
    · exact ⟨hPZ, Or.inl hZeq'⟩
    · exact ⟨hPZ, Or.inr ⟨hx, hy, hzZ⟩⟩
  · rintro ⟨hPZ, hZeq | ⟨hx, hy, hzZ⟩⟩
    · exact ⟨hPZ, Or.inl hZeq⟩
    · exact ⟨hPZ, Or.inr ⟨hx, hPZ, Or.inr ⟨hy, hzZ⟩⟩⟩

end Smash
end DomainTheory.NeighbourhoodSystems
