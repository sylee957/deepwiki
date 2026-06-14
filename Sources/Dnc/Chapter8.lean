import Book.Packetizer
import Book.PacketizerConcatenation
import Book.ServersResidualPriorityPackets
import Book.ServersResidualPgps
import Book.ServersResidualDrr
import Book.ServersDrr
import Book.ServersResidualWrr
import Book.ServersResidualWrrPackets
import Book.ServersWrr
import Book.ServersResidualTdma
import Sources.Dnc.Source

/-! # DNC catalog — Chapter 8: Packets
Book-numbered catalog entries for this chapter, each linked to the
`DeepWiki` library declaration that formalizes it (`alias`/`abbrev`),
or recorded as a note / unformalized item. -/

namespace DeepWiki.Dnc

open DeepWiki
open scoped NNReal ENNReal

/-- **Definition 8.1** (§8.1, p.184): Cumulative packet length sequence: an increasing sequence L = (L_n) with L_0 = 0 and some ℓ^l > 0 such that L_{n+1} ≥ L_n + ℓ^l; the values ℓ^l, ℓ^u are the minimum and maximum packet sizes. -/
abbrev def_8_1 := @IsPacketLengthSeq

/-- **Definition 8.2** (§8.1, p.185): Packetizer P^L: P^L(A)(0) = 0 and P^L(A)(t) = max { L_n | ∃ u < t, A(u) ≥ L_n }, releasing the largest cumulative packet length fully arrived strictly before t. -/
noncomputable def def_8_2 := @packetize

/-- **Lemma 8.1** (§8.1, p.185): For all A ∈ C and t > 0 there is n ∈ ℕ with P^L(A)(t) = L_n and L_n ≤ A(t) ≤ L_{n+1}: the packetizer value is attained at a cumulative packet length, sandwiching A(t). -/
alias lemma_8_1 := exists_packetize_eq

/-! **Proposition 8.1** (§8.1, p.186): A packetizer is a server: if L is a cumulative packet length sequence then P^L maps cumulative functions to cumulative functions (∀ A ∈ C, P^L(A) ∈ C) and is causal, A ≥ P^L(A). Library: isServer_packetizerRel, packetizeCurve_le, packetize_leftCont, packetize_pwc. -/

/-- **Corollary 8.1** (§8.1, p.186): Maximum buffer size of a packetizer: with maximum packet length ℓ^u the backlog of P^L is at most ℓ^u, i.e. A ≥ P^L(A) ≥ A − ℓ^u. -/
alias cor_8_1 := packetizeCurve_sandwich

/-- **Definition 8.3** (§8.1, p.187): P^L-packetized (P-packetized) cumulative function: A ∈ C is P^L-packetized iff A = P^L(A), the packetizer leaves it unchanged. -/
abbrev def_8_3 := @IsPacketized

/-- **Lemma 8.2** (§8.1, p.187): P^L is idempotent: P^L ∘ P^L = P^L. -/
alias lemma_8_2 := packetize_packetize

/-! **Theorem 8.1** (§8.1, p.187): Arrival curve after a packetizer: with maximum packet size ℓ^u, if A has a maximal (resp. minimal) arrival curve α^u (resp. α^l) then the packetized output D has maximal (resp. minimal) arrival curve α^u + ℓ^u (resp. α^l − ℓ^u). Library: isMaximalArrivalBound_packetizeCurve, isMinimalArrivalBound_packetizeCurve. -/

/-! **Theorem 8.2** (§8.1, p.188): Server/packetizer system S;P with max packet size ℓ^u: (1) if S offers min-plus β^m, maximal β^M and is a σ-shaper, then S;P offers β^m − ℓ^u, β^M, and is a (σ + ℓ^u)-shaper; (2) S;P outputs are P-packetized; (3) backlog of S;P differs from that of S by at most ℓ^u; (4) on P-packetized input, P adds no delay, d(A,S;P) = d(A,S). Library: IsMinimalServiceCurve.comp_packetizerRel, IsMaximalServiceCurve.comp_packetizerRel, IsShaper.comp_packetizerRel, isPacketized_of_comp_packetizerRel, Deviation.backlog_packetizeCurve_sandwich, Deviation.delay_packetizeCurve_eq, not_forall_isStrictMinimalServiceCurve_comp_packetizerRel. -/

/-! **Corollary 8.2** (§8.1, p.190): Packetizer as a delay: if a cumulative function A is P-packetized then S;P offers the pure-delay min-plus service curve δ_{d(A,S)} to A (using d(A,S;P) = d(A,S)). Library: Deviation.delay_packetizeCurve_eq, exists_delay_eq_of_comp_packetizerRel. -/

/-! **Corollary 8.3** (§8.1, p.190): Arrival curve from a packetizer: if S is a server, P a packetizer with max packet size ℓ^u, (A,C) ∈ S;P, P-packetized, and S maximal-arrival σ^M-shaper, then C has maximal arrival curve ((α ∘ β^M) ∧ (σ + ℓ^u)) ∧ (α ⊘ δ_{hDev(A,S;P)}). Not formalized in the library. -/

/-- **Definition 8.3.1** (§8.2.1, p.191): Non-preemptive static priority (NP-SP): a backlogged higher-or-equal-priority flow is served except for at most one in-service lower-priority packet (≤ max packet size of lower priorities). -/
abbrev def_8_3_1_npsp := @IsNpsp

/-- **Theorem 8.3** (§8.2.1, p.193): NP-SP residual (min-plus), eq [8.8]: an NP-SP n-server with aggregate strict service curve β and higher-priority arrival curves α_j gives flow i the min-plus service curve β_i = [β − ∑_{j<i} α_j − max_{i<j≤n} ℓ_j^u]^+↑. -/
alias thm_8_3_a := isMinimalServiceCurve_residualServer_of_isNpsp

/-- **Theorem 8.3** (§8.2.1, p.193): NP-SP residual (strict), eq [8.9]: under the same hypotheses flow i is offered the strict service curve β_i^s = [β − ∑_{j<i} α_j − max_{i≤j≤n} ℓ_j^u]^+↑ (max extended to its own priority). -/
alias thm_8_3_b := isStrictMinimalServiceCurve_residualServer_of_isNpsp

/-! **Theorem 8.4** (§8.2.2, p.196): Packetized GPS (PGPS): an n-server with GPS parameters φ_1,…,φ_n which is a λ_R-greedy shaper; if the GPS server offers flow i the strict service curve β_i^GPS, then the PGPS server offers it the min-plus service curve β_i^PGPS = [β_i^GPS − ℓ^u]^+ (ℓ^u upper bound on packet length). Library: pgpsResidual, minConv_pgpsResidual_le_of_isPgpsTracking, IsPgpsTracking. -/

/-- **Definition 8.1** (§8.2.3, p.198): Algorithm 1 (DRR): per-round each backlogged flow's deficit counter gains its quantum Q_i, then head packets are drained while they fit; an emptied queue resets the counter to 0. -/
noncomputable def alg_8_1_drr := @drrServe

/-- **Theorem 8.5** (§8.2.3, p.197): DRR residual service curve, eq [8.10]: a DRR n-server with strict aggregate β, quantum Q_i, max packet length ℓ_i^u offers flow i the strict service curve β_i^DRR = [Q_i/F·β − (Q_i(L−ℓ_i^u)+(F−Q_i)(Q_i+ℓ_i^u))/F]^+, with F = ∑ Q_j, L = ∑ ℓ_j^u. -/
alias thm_8_5 := isStrictMinimalServiceCurve_drrResidual_of_isDrr

/-- **Definition 8.2** (§8.2.4, p.200): Algorithm 2 (WRR): per-round each non-empty flow sends up to w_i head packets in turn. -/
abbrev alg_8_2_wrr := @wrrServe

/-! **Definition 8.4** (§8.2.4, p.200): Packet curves: for a cumulative packet length sequence L = (L_n) and nondecreasing L^l, L^u : ℕ → ℝ≥0, L^l and L^u are lower and upper packet curves iff ∀ i,n, L^l(n) ≤ ∑_{j=i+1}^{i+n} L_j ≤ L^u(n). Library: IsWrrPackets. -/

/-- **Theorem 8.6** (§8.2.4, p.200): WRR residual service curve, eq [8.10] (packet-curve form): a WRR n-server with weights w_i and lower/upper packet curves L_i^l, L_i^u, aggregate strict β, offers flow i the strict service curve f^{-1} ∘ β (f the worst-round-count price, f^{-1} its lower pseudo-inverse). -/
alias thm_8_6_a := isStrictMinimalServiceCurve_wrrResidualPackets_of_isWrrPackets

/-- **Theorem 8.6** (§8.2.4, p.200): WRR residual service curve, eq [8.11] (staircase form): flow i is offered the strict service curve (λ_1 ∗ ν_{q_i,q_i+Q_i}) ∘ [β − Q_i]^+, with q_i = w_iℓ_i^l and Q_i = ∑_{j≠i} w_jℓ_j^u. -/
alias thm_8_6_b := isStrictMinimalServiceCurve_wrrResidualStaircase_of_isWrr

/-- **Theorem 8.6** (§8.2.4, p.200): WRR residual service curve, eq [8.12] (linearized ratio form): flow i is offered the strict service curve q_i/(q_i+Q_i)·[β − Q_i]^+. -/
alias thm_8_6_c := isStrictMinimalServiceCurve_wrrResidual_of_isWrr

/-- **Theorem 8.7** (§8.2.5, p.203): TDMA residual service curve: an n-server with guaranteed rate λ_R under TDMA with cycle c, flow-i slot s_i ≥ ℓ_i^u/R, and packet lengths in [ℓ_i^l, ℓ_i^u], guarantees flow i the strict service curve β_i^TDMA = ν_{c,o_i,−T_i} ∗ β_{R,T_i} with T_i = ℓ_i^u/R + c − s_i and o_i = ℓ_i^u⌊Rs_i/ℓ_i^u⌋ (equal lengths) or o_i = ℓ_i^l ∨ (Rs_i − ℓ_i^u) otherwise. -/
alias thm_8_7 := isStrictMinimalServiceCurve_tdmaResidual_of_isTdma

end DeepWiki.Dnc
