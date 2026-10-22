module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumSys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.fromS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.dsharpEquiv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.inSharp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.pairSharp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embR
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_inter_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_subset_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_subset_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Gamma_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.memS_subset_gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.memS_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.memS_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.memS_embZero_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.memS_embPair_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.prod_dsharp_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sum_mem_inj₀_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sum_mem_inj₁_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumSys_mem_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_ne_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_ne_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_ne_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.fromS_mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.fromS_mem_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.fromS_toS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS_fromS

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}


section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD


/-- **Example 6.1 (Scott 1981, PRG-19) — the domain equation `D^§ ≅ D + (D^§ × D^§)`.** The tree
algebra `D^§` is, as a domain, isomorphic to `D + (D^§ × D^§)` — Scott's defining isomorphism, "as can
be seen by reference to the equation for `D^§` and the definitions of `+` and `×`". -/
theorem dsharp_domain_equation :
    Dsharp D hD ≅ᴰ sum D (prod (Dsharp D hD) (Dsharp D hD)) hD (prod_dsharp_nonempty D hD) :=
  ⟨dsharpEquiv D hD⟩


/-- **Example 6.1 (Scott 1981, PRG-19).** `λx. x^§` is an *isomorphic injection*: `x^§ ⊑ x'^§ ↔ x ⊑ x'`
(in particular one-one). -/
theorem inSharp_le_iff {x x' : D.Element} : inSharp D hD x ≤ inSharp D hD x' ↔ x ≤ x' := by
  constructor
  · intro h X hX
    rcases h (embZero X) (Or.inr ⟨X, hX, rfl⟩) with h0 | ⟨X', hX', heq⟩
    · exact absurd h0 (embZero_ne_Gamma D hD X)
    · rw [← embZero_injective heq] at hX'; exact hX'
  · intro h W hW
    rcases hW with rfl | ⟨X, hX, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨X, h _ hX, rfl⟩


/-- **Example 6.1 (Scott 1981, PRG-19).** `λx, y. ⟨x, y⟩` is an *isomorphic injection*:
`⟨x, y⟩ ⊑ ⟨x', y'⟩ ↔ x ⊑ x' ∧ y ⊑ y'`. -/
theorem pairSharp_le_iff {x x' y y' : (Dsharp D hD).Element} :
    pairSharp D hD x y ≤ pairSharp D hD x' y' ↔ x ≤ x' ∧ y ≤ y' := by
  constructor
  · intro h
    refine ⟨fun P hP => ?_, fun Q hQ => ?_⟩
    · rcases h (embPair P (Gamma D)) (Or.inr ⟨P, Gamma D, hP, y.master_mem, rfl⟩) with
        h0 | ⟨P', Q', hP', hQ', heq⟩
      · exact absurd h0 (embPair_ne_Gamma D hD P (Gamma D))
      · obtain ⟨hPP, -⟩ := embPair_injective heq; rw [← hPP] at hP'; exact hP'
    · rcases h (embPair (Gamma D) Q) (Or.inr ⟨Gamma D, Q, x.master_mem, hQ, rfl⟩) with
        h0 | ⟨P', Q', hP', hQ', heq⟩
      · exact absurd h0 (embPair_ne_Gamma D hD (Gamma D) Q)
      · obtain ⟨-, hQQ⟩ := embPair_injective heq; rw [← hQQ] at hQ'; exact hQ'
  · rintro ⟨hx, hy⟩ W hW
    rcases hW with rfl | ⟨P, Q, hP, hQ, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨P, Q, hx _ hP, hy _ hQ, rfl⟩

end Equation

end Example61

end DomainTheory.NeighbourhoodSystems
