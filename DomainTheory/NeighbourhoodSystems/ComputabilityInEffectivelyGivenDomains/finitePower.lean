module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.powerDomainEffective

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section
variable {α : Type*} (V : NeighborhoodSystem α)

def PDfinJoinZero : V.PowerDomain.Element := V.PowerDomain.bot

def PDmemFinJoin {n : ℕ} (xs : Fin n → V.Element) (W : Set (Set α)) : Prop :=
  ∃ (X : Fin n → Set α) (_hX : ∀ i, (xs i).mem (X i)),
    V.PowerDomain.mem W ∧ ∀ i, V.upSet (X i) ⊆ W

def PDfinJoinSucc {m : ℕ} (xs : Fin (m + 1) → V.Element) : V.PowerDomain.Element where
  mem := V.PDmemFinJoin xs
  sub hW := by obtain ⟨_, _, hPD, _⟩ := hW; exact hPD
  master_mem := by
    refine ⟨fun i => V.master, fun i => (xs i).master_mem, V.PDmem_master, fun i Z hz => hz⟩
  inter_mem h1 h2 := by
    obtain ⟨X1, hX1, hPD1, hsub1⟩ := h1
    obtain ⟨X2, hX2, hPD2, hsub2⟩ := h2
    refine ⟨fun i => X1 i ∩ X2 i, fun i => (xs i).inter_mem (hX1 i) (hX2 i),
      V.PDmem_inter hPD1 hPD2, fun i Y hY => ?_⟩
    rw [← V.upSet_inter] at hY
    rcases hY with ⟨hY1, hY2⟩
    exact ⟨hsub1 i hY1, hsub2 i hY2⟩
  up_mem h hW hsub := by
    obtain ⟨X, hX, _, hsub'⟩ := h
    exact ⟨X, hX, hW, fun i => (hsub' i).trans hsub⟩

end
end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section
variable {α : Type*} (V : NeighborhoodSystem α)

def PDfinJoin (n : ℕ) (xs : Fin n → V.Element) : V.PowerDomain.Element :=
  match n with
  | 0 => V.PDfinJoinZero
  | _m + 1 => V.PDfinJoinSucc xs

@[simp] theorem PDmem_finJoinZero {W : Set (Set α)} :
    (V.PDfinJoinZero).mem W ↔ W = V.PowerDomain.master := by
  rw [PDfinJoinZero, mem_bot, PowerDomain_master]

def PDsingleton (x : V.Element) : V.PowerDomain.Element := V.PDfinJoin 1 (fun (_ : Fin 1) => x)

theorem PDmem_finJoinSucc {m : ℕ} (xs : Fin (m + 1) → V.Element) {W : Set (Set α)} :
    (V.PDfinJoinSucc xs).mem W ↔ V.PDmemFinJoin xs W := Iff.rfl

@[simp] theorem PDmem_singleton {x : V.Element} {W : Set (Set α)} :
    (V.PDsingleton x).mem W ↔
      ∃ X, x.mem X ∧ V.PowerDomain.mem W ∧ V.upSet X ⊆ W := by
  rw [PDsingleton, PDfinJoin, PDmem_finJoinSucc, PDmemFinJoin]
  constructor
  · rintro ⟨X, hX, hPD, hsub⟩
    exact ⟨X 0, hX 0, hPD, hsub 0⟩
  · rintro ⟨X, hX, hPD, hsub⟩
    refine ⟨fun _ => X, fun _ => hX, hPD, fun _ => hsub⟩

theorem PDmem_finJoin {n : ℕ} (xs : Fin n → V.Element) {W : Set (Set α)} :
    (V.PDfinJoin n xs).mem W ↔
      if n = 0 then W = V.PowerDomain.master else V.PDmemFinJoin xs W := by
  match n with
  | 0 => simp [PDfinJoin, PDfinJoinZero, mem_bot]
  | m + 1 => simp [PDfinJoin, PDfinJoinSucc]

theorem PDmem_finJoin_iUnion {m : ℕ} (xs : Fin (m + 1) → V.Element) {W : Set (Set α)} :
    (V.PDfinJoinSucc xs).mem W ↔
      ∃ (X : Fin (m + 1) → Set α) (_hX : ∀ i, (xs i).mem (X i)),
        V.PowerDomain.mem W ∧
          (⋃ i, V.upSet (X i)) ⊆ W := by
  rw [PDmem_finJoinSucc]
  constructor
  · rintro ⟨X, hX, hPD, hsub⟩
    exact ⟨X, hX, hPD, Set.iUnion_subset hsub⟩
  · rintro ⟨X, hX, hPD, hsub⟩
    exact ⟨X, hX, hPD, (Set.iUnion_subset_iff).mp hsub⟩

end

end NeighborhoodSystem
section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β γ : Type*}

namespace NeighborhoodSystem

variable (V : NeighborhoodSystem α)

theorem PDmem_down {A : Set (Set α)} (hA : V.PDmem A) {Z X : Set α}
    (hZ : Z ∈ A) (hXZ : X ⊆ Z) (hX : V.mem X) : X ∈ A := by
  obtain ⟨L, hL, rfl⟩ := hA
  obtain ⟨X', hX', _, hZsub⟩ := (V.mem_PDunion).mp hZ
  exact (V.mem_PDunion).mpr ⟨X', hX', hX, hXZ.trans hZsub⟩

end NeighborhoodSystem
end

end DomainTheory.NeighbourhoodSystems
