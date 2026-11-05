module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_1a

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Scott Factoid 1.1b: if $n > 0$, then
$\bigcap_{i < n} X_i = (\bigcap_{i < n-1} X_i) \cap X_{n-1}$. -/
theorem factoid_1_1_b (X : ℕ → Set α) {n : ℕ} (hn : 0 < n) :
    V.interUpTo X n = V.interUpTo X (n - 1) ∩ X (n - 1) := by
  cases n with
  | zero => exact (Nat.not_lt_zero _ hn).elim
  | succ n =>
    rw [Nat.add_one_sub_one]
    exact interUpTo.succ V X n

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
