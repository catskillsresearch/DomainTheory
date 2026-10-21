/-ai
The second projection relates the sharp neighbourhood coded by m to the sharp neighbourhood coded by k exactly when k is zero, or m is even and nonzero and the sharp neighbourhood of the right component of m divided by two, minus one, is contained in the neighbourhood coded by k.

Both codes denote sharp neighbourhoods, and equality with the master neighbourhood is equality of the code with zero. The zero neighbourhood is never a paired embedding, and its code is zero. An odd neighbourhood is a zero embedding, hence not a paired embedding, and an odd code is not even. An even neighbourhood is a paired embedding, the arithmetic identity recovers the child index, and injectivity of the paired embedding identifies the right-hand child.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Combinators77
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


/-- The index characterization of `proj1Map`. `V_m proj₁ V_k` iff `k = 0` (`V_k = Γ`) or `m` is an
even node index `2a+2` with `V_{q a} ⊆ V_k` (the *right* child, `q a = a.unpair.2`). -/
theorem proj1_rel_Vsharp_iff (P : ComputablePresentation D) (m k : ℕ) :
    (proj1Map hD).rel (Vsharp D P m) (Vsharp D P k) ↔
      k = 0 ∨ (m % 2 = 0 ∧ m ≠ 0 ∧ Vsharp D P (m / 2 - 1).unpair.2 ⊆ Vsharp D P k) := by
  rw [proj1Map_rel, and_iff_right (Vsharp_mem P m), and_iff_right (Vsharp_mem P k)]
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
    · rintro ⟨Pp, Qq, heq, hQk⟩
      obtain ⟨-, hQ⟩ := embPair_injective heq
      exact ⟨by omega, by omega, by rw [hQ]; exact hQk⟩
    · rintro ⟨-, -, hsub⟩
      exact ⟨Vsharp D P a.unpair.1, Vsharp D P a.unpair.2, rfl, hsub⟩

end Proposition77
end DomainTheory.NeighbourhoodSystems
