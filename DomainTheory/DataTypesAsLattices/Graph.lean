/-ai
This file gathers and re-exports the graph development of Scott's section 1: the basic vocabulary, membership in a graph and in an application, monotonicity of application on each side, the monotonicity law, Scott continuity of application, the three clauses and the combined statement of Theorem 1.2, the equality of abstraction with the graph, and the beta law.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Graph.Basic
public import DomainTheory.DataTypesAsLattices.Graph.mem_graph
public import DomainTheory.DataTypesAsLattices.Graph.mem_funOf
public import DomainTheory.DataTypesAsLattices.Graph.funOf_monotone_right
public import DomainTheory.DataTypesAsLattices.Graph.funOf_monotone_left
public import DomainTheory.DataTypesAsLattices.Graph.mu_law
public import DomainTheory.DataTypesAsLattices.Graph.funOf_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2_i
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2_ii
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2_iii
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2
public import DomainTheory.DataTypesAsLattices.Graph.lam_eq_graph
public import DomainTheory.DataTypesAsLattices.Graph.beta

@[expose] public section
