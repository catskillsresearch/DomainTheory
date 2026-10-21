/-ai
The smash product carries the subsystem relation componentwise.

The masters agree by rewriting the two component masters inside the product neighbourhood. Membership sends the master to the master by that equality, and a proper rectangle along the two subsystems, rewriting properness by the component master equalities. For intersections, two masters remain the master, and a master meeting a proper rectangle reduces by the componentwise intersection of product neighbourhoods, because each coordinate lies under its master. Two proper rectangles rewrite the intersection as the rectangle of the intersected coordinates. The left intersection is still distinct from the larger left master, by the left-factor intersection lemma and the left master equality, so the inverse membership lemma supplies both component memberships in the larger systems. The two subsystem intersection laws close them, and properness of both coordinates is again the left-factor intersection lemma.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.otimesTok_mem_prod_inv

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}


variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}


variable {A₀ A₁ B₀ B₁ : ScottSys}

/-- The smash product carries the subsystem relation componentwise. -/
theorem otimesTok_subsystem (h0 : A₀.sys ◁ B₀.sys) (h1 : A₁.sys ◁ B₁.sys) :
    (A₀.otimes A₁).sys ◁ (B₀.otimes B₁).sys := by
  have heqm : prodTokNbhd A₀.sys.master A₁.sys.master
      = prodTokNbhd B₀.sys.master B₁.sys.master := by rw [h0.master_eq, h1.master_eq]
  refine ⟨heqm, ?_, ?_⟩
  · rintro W (rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩)
    · exact Or.inl heqm
    · exact Or.inr ⟨X, Y, h0.sub hX, h1.sub hY, h0.master_eq ▸ hXne, h1.master_eq ▸ hYne, rfl⟩
  · rintro W W' (rfl | ⟨X, Y, hX, hY, hXne, hYne, rfl⟩)
      (rfl | ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩) hInt
    · rw [Set.inter_self]; exact Or.inl rfl
    · rw [prodTokNbhd_inter, Set.inter_eq_right.mpr (A₀.sys.sub_master hX'),
        Set.inter_eq_right.mpr (A₁.sys.sub_master hY')]
      exact Or.inr ⟨X', Y', hX', hY', hX'ne, hY'ne, rfl⟩
    · rw [Set.inter_comm, prodTokNbhd_inter, Set.inter_eq_right.mpr (A₀.sys.sub_master hX),
        Set.inter_eq_right.mpr (A₁.sys.sub_master hY)]
      exact Or.inr ⟨X, Y, hX, hY, hXne, hYne, rfl⟩
    · rw [prodTokNbhd_inter] at hInt ⊢
      have hXne' : X ∩ X' ≠ B₀.sys.master := by
        rw [← h0.master_eq]; exact inter_ne_of_ne_left (A₀.sys.sub_master hX) hXne
      obtain ⟨hmemX, hmemY⟩ := otimesTok_mem_prod_inv hInt hXne'
      exact Or.inr ⟨X ∩ X', Y ∩ Y', h0.inter_closed hX hX' hmemX, h1.inter_closed hY hY' hmemY,
        inter_ne_of_ne_left (A₀.sys.sub_master hX) hXne,
        inter_ne_of_ne_left (A₁.sys.sub_master hY) hYne, rfl⟩

end Exercise619
end DomainTheory.NeighbourhoodSystems
