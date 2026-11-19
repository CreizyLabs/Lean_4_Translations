# Formal Archival Replications in Lean 4 (1960–1971)

![Kernel Verification](https://img.shields.io/badge/Kernel_Verification-Passing-brightgreen)
![Lean 4](https://img.shields.io/badge/Lean_4-v4.15.0-blue)
![Sorries](https://img.shields.io/badge/sorry-0-brightgreen)
![Custom Axioms](https://img.shields.io/badge/custom_axioms-0-brightgreen)
![License](https://img.shields.io/badge/License-Apache_2.0-blue.svg)

A collection of complete, zero-axiom, zero-`sorry` formalizations of historical computing architectures, magnetic-core physics, ternary error-correcting codes, and early flight/microprocessor verification suites in Lean 4.

Every specification in this repository is translated directly from primary archival literature (Soviet Academy of Sciences proceedings, Moscow State University and Tajik State University monographs, MIT Instrumentation Laboratory AGC assembly listings, and Intel MCS-4 characterization datasheets) and verified in the Lean 4 kernel.

---

## Verification Guarantees

* **Zero `sorry` / Zero Custom `axiom`s**: Every theorem is constructively proved using structural induction, linear integer arithmetic (`omega`), polynomial ring normalization (`ring`), or finite-domain bit/trit-blasting (`decide` / `rfl`).
* **Full-Stack Fidelity**: Formalizations span from physical magnetomotive force ($\text{MMF}$) and magnetic amplifier flux transfer curves up through instruction-set execution engines, hardware interrupt handlers, and application-level numerical/scheduling algorithms.
* **Executable Semantics**: All machine models are total, purely functional state machines with executable test benches (`#eval`).

---

## Repository Architecture & Primary Sources

| Module | System / Era | Primary Archival Source | Scope of Formalization |
| :--- | :--- | :--- | :--- |
| **`Setun/Setun_1960.lean`** | **MSU Setun** (1960) | N. P. Brusentsov, *Вычислительная машина «Сетунь» Московского государственного университета*, Kiev Symposium on Cybernetics, pp. 226–233 (1960). | Balanced ternary alphabet $\{-1, 0, +1\}$, 3-input serial full adder with single carry flip-flop, 18-trit fixed-point scaling ($3^{16} = 43,046,721$), 5th-trit addressing modes (`fullWord`, `seniorHalfWord`, `juniorHalfWord`), dual condition flags ($\omega_+$ and $\omega_\gamma$), all 24 Table 1 opcodes, drum/RAM zone transfers, and Page 226 Author's Errata cycle timings ($325\,\mu\text{s}$ multiplication). |
| **`Setun/Magnetic_Digital_Elements_1964.lean`** | **Pulse-Current Magnetic Amplifiers & Ferrite Laddics** (1964) | *Магнитные элементы автоматики, телемеханики, измерительной и вычислительной техники*, Naukova Dumka, Kiev, pp. 285–291, 361–366, 480–487 (1964). | **1. Olshvang**: Core testing equations ($\Delta B, H_y$) and dual connector windings ($w_p = 24, w_y = 14$).<br>**2. Brusentsov**: Pulse-current magnetic amplifier gates (`magInhibit`, `magAnd`, `magOr`), the 6 electrical fan-out/interconnection rules, 2-bit binary decoder (Fig. 7), dual-rail mutual-inhibition ternary cell (Fig. 8), 2-trit 9-output ternary decoder (Fig. 9), and the ternary half-adder algebraic identity $3Q + S = A + B$ (Fig. 10).<br>**3. Nezhivov & Ryabinin**: 14-rung ferrite ladder (`лесенка` / Laddic) Boolean product-of-sums, blocking factor $K_b = \frac{m + 2(N-n)L}{2m + 2(N-1)L}$, and $\text{MMF}$ equivalence $M_n = K_b M_1$.<br>**4. Chinaev**: Extremal regulator quadratic functional $Q = \sum (\Delta x_i)^2 \ge 0$. |
| **`Setun/Setun70_1971.lean`** | **Setun-70 Two-Stack EDS Architecture** (1971) | N. P. Brusentsov & E. A. Zhogolev, *Структура и алгоритм функционирования малой вычислительной машины «Сетунь-70»*, Vychislitel'naya Tekhnika i Voprosy Kibernetiki, Vol. 8, LGU, pp. 34–51 (1971). | Complete ALGOL-60 hardware specification translated to Lean 4: 6-trit syllables ($3^6 = 729$, $[-364..+364]$), 18-trit 3-syllable words, 27 Level-1 pages (9 RAM, 18 ROM) $\times$ 81 syllables, Level-2 page memory $f[-1:1, -3280:3280, -40:40]$, all 27 Basic RPN operations (`B1..B27`), all 27 Special/Privileged operations (`S1..S27`), `REFSYL`, `MACRO`, `INCRC`, and the 13 hardware interrupt vectors $w \in \{-40..-28\}$. |
| **`Setun/Setun_Minsk22_Dushanbe_1971.lean`** | **Symmetric Ternary Hamming Codes, BVP & CPM Scheduling** (1971) | Ed. I. U. Soliev, *Вопросы технического и математического обеспечения ЭЦВМ «Сетунь» и «Минск-22»*, Tajik State University, Dushanbe, pp. 1–112 (1971). | **Ch. 1–2 (Soliev)**: TGU Setun 1965–1970 utilization reconciliation and magnetic amplifier thermal/noise thresholds ($+10^\circ\text{C}..+70^\circ\text{C}$, $20\%$ noise rejection, $80\%$ regeneration).<br>**Ch. 3 (Yukhanonov)**: Linear conjugation boundary value problem, Noether-Mikhailov index identity $l - p = 2\kappa$, and contraction mapping series.<br>**Ch. 4 (Rumyantsev & Soliev)**: Symmetric ternary Hamming codes over $\{-1, 0, +1\}$, sphere-packing bound $3^m \ge 2(m+n)+1$, syndrome locator $N = |\sigma|$, error corrector $\Delta_N = -\text{sign}(\sigma)$, and exhaustive verification of the $(11, 8)$ code across all 11 positions.<br>**Ch. 8–9 (Kurtakov)**: Fixed-point linear system solver $x_{n+1} = \alpha x_n + \beta$ and 18-trit packed Critical Path Method (CPM) scheduler ($T_i^{(0)}, T_i^{(1)}, R_{i,j}, r_{i,j}$) verified on the 10-event network graph. |
| **`Setun/CrossLayerBridge.lean`** | **1964 Physics $\leftrightarrow$ 1960 ALU Isomorphism** | Cross-module formal bridge (`Setun/Magnetic_Digital_Elements_1964` $\to$ `Setun/Setun_1960`). | Proves (`brusentsov_1964_half_adder_eq_setun_1960_adder`) that Brusentsov's 1964 dual-rail pulse-current magnetic amplifier half-adder equations compute the exact same `(sum, carry_out)` values as the 1960 Setun serial full-adder (`Trit.fullAdder a b .zero`). |
| **`ApolloMission/AGCBlockTwoReplication.lean`** | **Apollo Guidance Computer Block II** (1969) | MIT Instrumentation Lab, *Comanche 055 (Colossus 2A)*, `AGC_BLOCK_TWO_SELF-CHECK.agc`. | Native `BitVec 16` 1's complement hardware arithmetic with end-around carry (`onesComplementAdd`), Erasable/Fixed Core Rope memory state, and `ERASCHK`, `CNTRCHK`, `CYCLSHFT`, and `BNKCHK` self-check routines. Features a **universal structural induction proof** (`eraschkLoop_universal_correct`) proving non-destructive scratchpad verification over arbitrary address ranges in $O(1)$ kernel steps without loop unrolling. |
| **`ApolloMission/executive_agc.lean`** | **Apollo Guidance Computer (Executive Routine)** (1969) | MIT Instrumentation Lab, *Comanche 055 (Colossus 2A)*, `EXECUTIVE.agc`, pp. 1208–1220. | Complete priority-based cooperative job scheduler for the AGC Block II: 15-bit ones'-complement arithmetic, hardware registers (`A`, `L`, `Q`, `EBANK`, `FBANK`, `BBANK`, `Z`), 7 Core Sets (`0..6`), VAC area allocation (`VAC1..VAC5`), `-CCSPR` instruction word offset recovery, `NOVAC`, `FINDVAC`, `CHANG1` context switching, `PRIOCHNG`, `JOBSLEEP`, `JOBWAKE`, `ENDOFJOB`, and dispatch to `SELFCHK`. Includes 9 kernel-verified step theorems. |
| **`ApolloMission/interpreter_agc.lean`** | **Apollo Guidance Computer (Interpretive Language Engine)** (1969) | MIT Instrumentation Lab, *Comanche 055 (Colossus 2A)*, `INTERPRETER.agc`, pp. 1107–1199. | Complete formal specification of Hal Laning's AGC Polish-notation bytecode virtual machine: multi-precision fixed-point vector and matrix arithmetic, editing registers (`CYR`, `SR`, `CYL`, `EDOP`), bank-switching (`SUPERBNK`), double-precision multiply (`DMPSUB`), rounding (`ROUNDSUB`), and kernel-verified execution proofs. |
| **`ApolloMission/LEM_GEOMETRY.lean`** | **Apollo 11 Lunar Module (LEM Geometry & Rendezvous Radar)** (1969) | MIT Instrumentation Lab, *Luminary 1A (Build 099)*, `LEM_GEOMETRY.agc`, pp. 320–325. | Complete formalization of `SVDWN2`, `SVDWN1`, `RRANGLES`, `RRNB`, and `RRNBMPAC`: `AVEMIDSW` guard, `X2`-indexed B-27/B-5 $\to$ B-29/B-7 scaling, 1's-to-2's complement CDU roundtrip (`2V1STO2S` / `CDULOGIC`), `RADMODES`/`ANTENBIT` 3-step `DXCH` swap, Y-axis gimbal lock (`BOVB LUNDESCH`), and exact algebraic proof that Mode 1 `(T, S)` and Mode 2 `(180° - T, S + 180°)` yield identical unit Line-of-Sight vectors. |
| **`ApolloMission/PLANETARY_INERTIAL_ORIENTATION.lean`** | **Apollo 11 Lunar Module (Planetary Orientation & Libration)** (1969) | MIT Instrumentation Lab, *Luminary 1A (Build 099)*, `PLANETARY_INERTIAL_ORIENTATION.agc`, pp. 1140–1148. | Complete formalization of `RP-TO-R`, `R-TO-RP`, `MOONMX`/`MOONMXA`, `NEWANGLE`, `EARTHMX`, and `EARTHL`: exact Euler-angle factorization of `MOONMX`, universal $SO(3)$ orthogonality and $\det = 1$ proofs for both Earth and Moon matrices, exact first-order libration cancellation (`R-TO-RP(RP-TO-R(rp)) = rp - LP × (LP × rp)`), exact Pythagorean norm identity, and exact triple-precision `NEWANGLE` bit-alignment across `WEARTH`, `FDOT`, `BDOT`, and `NODDOT`. |
| **`ApolloMission/THE_LUNAR_LANDING.lean`** | **Apollo 11 Lunar Module (P63 Braking Phase & P68 Landing Confirmation)** (1969) | MIT Instrumentation Lab, *Luminary 1A (Build 099)*, `THE_LUNAR_LANDING.agc`, pp. 785–792. | Complete formalization of `P63LM`, `FLAGORGY`, `IGNALG`, `DDUMCALC`, `DDUMGOOD`, `R60INIT`, `P63SPOT2`/`3`/`4`, and `P68` (`LANDJUNK`): `CHAN12` bit 14 track-enable clear, `DDUMCALC` zero-at-target convergence and strict positive-denominator safety (`KIGNX/B4 < 0`), `OUTOFPLN` vanishing in the orbital plane, `CHAN33` bit 6 Landing Radar Position 1 interlock (`CODE500`), `P68` abort lockout, and cross-module Apollo 11 flight-chain theorems (`SVDWN2` $\to$ `VSL2` $\to$ `R-TO-RP` and `P63` $\leftrightarrow$ `P68` `RLS` roundtrip). |
| **`StoryOfMel/MelLGP30.lean`** | **LGP-30 Computer Simulator (`mel.c`)** (1956/1995) | George Weigt, *LGP-30 Simulator for Mel Kaye's Blackjack Program* (`mel.c`). | Exact 32-bit/64-bit LGP-30 word & drum arithmetic, 4096-word drum memory (`64 × 64`), 128-entry Flexowriter output/input tables (`ptab`, `rtab`), 16-opcode instruction execution, `loadProgramFromString` tape parser, and universal memory-size & PC bounds preservation proofs. |
| **`StoryOfMel/BkjckTape.lean`** | **Mel Kaye's LGP-30 Blackjack Tape** (1959) | Mel Kaye, *Royal McBee LGP-30 Blackjack Machine-Code Tape* (`bkjck.tx.txt`). | All 10 verbatim tracks (Tracks 45–54, 640 32-bit machine words) with compile-time kernel verification of exact 29-bit LGP-30 paper-tape checksums (`bkjck_full_tape_verified`). |
| **`StoryOfMel/NatherStoryOfMel.lean`** | **The Story of Mel (RPC-4000 Testless Loop)** (1983) | Ed Nather, *Real Programmers Don't Use Fortran, Either!* (Usenet `nather.txt`, May 21, 1983). | RPC-4000 revolving drum timing model ("optimum" vs. "most pessimum"), console sense switch cheat test, and universal algebraic proof of Mel's testless loop overflow (`mel_testless_loop_exits_to_zero`). |
| **`Intel4004/intel4004.lean`** | **Intel 4004 MCS-4 Microprocessor** (1971) | Intel Corporation, *MCS-4/40 Component Data Catalog: 4004 Single Chip 4-Bit P-Channel Microprocessor*, pp. 8-15 to 8-23 (1971). | Complete 4-bit CPU, 16 index registers ($R_0..R_{15}$ / pairs $P_0..P_7$), 4-level 12-bit address stack, `CM-RAM0..3` bank decoder (`DCL`), `SRC` latch, 8$\times$4$\times$4$\times$16 RAM main & status arrays, all 46 instructions (256-byte opcode table), $I_{DD}$ temperature/voltage model, and a kernel-proved 29-cycle (232-clock) machine-code execution suite. |
| **`LAPACK/DGESV.lean`** | **Netlib LAPACK General Linear Solver** (1992) | Netlib LAPACK 3.x, `dgesv.f`, `dgetrf.f`, `dgetf2.f`, `dgetrs.f`, `dlaswp.f`, `dtrsm.f`. | Complete zero-axiom, zero-sorry formalization of LAPACK general linear system solver $AX = B$ over exact arithmetic (`Rat` / generic `LAPACKField`). Transcribes full Fortran 77 dependency tree with explicit 1-based indexing, partial pivoting, permutation composition, triangular back-substitution, parameter validation theorems (`dgesv_illegal_n`, etc.), and singular matrix propagation. |
| **`TempleOS/TempleOS.lean`** | **TempleOS Operating System Core** (2013) | Terry A. Davis, *TempleOS Version 5.03*, `Kernel/Dsk/DskStrA.HC`, `Kernel/Compress.HC`, `Compiler/`. | Complete zero-axiom formalization of TempleOS 64-bit architecture: RedSea 64-bit filesystem directory records and cluster allocators, CArcCompress LZW decompressor (`expand_buf`) with verified universal output bounds (`lzwOuterLoop_size_le`), and HolyC operator precedence parser with Pratt precedence binding. |
| **`ColdWarDefense/SageProgramming.lean`** | **USAF SAGE Air Defense Command** (1961) | USAF Air Defense Command / SDC, *SAGE Computer Programming & System Training Office*, ADCM 55-32 & ADCR 50-3 (24 April 1961). | SAGE System Model artifacts (`CCA`, `DCA`, `DCS`, `ODAP`, `SSTP`), 12-step lifecycle & Chart 2 lead-time verification (`13..52` months), ADCM 55-32 SPC approval workflow state machine with universal governance safety proof (`spc_installed_requires_full_approval`), Priority-1 emergency bypass, and ADCR 50-3 STU escalation chain. |
| **`ColdWarDefense/ImpHardware.lean`** | **Honeywell DDP-516 ARPANET IMP Hardware** (1970) | Honeywell Doc. No. 70130072261A, *INTERMODEM PROCESSOR SYSTEM Instruction Manual* (January 1970, prepared for BBN). | Table 4-1 DMC/PI assignment injectivity, Section III OCP instruction decoder, False-DLE (`0x10`) byte-stuffing universal round-trip (`unstuffDLE_stuffDLE`), Watch Dog Timer 2/6/10/12-minute schedule, Halt Inhibit & power-fail override, Sector 1 & locations `0o60`/`0o62` memory lockout invariance, 16-bit host message padding alignment, and μ-PAC NAND circuits. |
| **`ColdWarDefense/ImpCodeResurrection.lean`** | **ARPANET IMP Program & 1970 Topology** (1969–2013) | The IMP Software Guys, *The ARPANET IMP Program: Retrospective and Resurrection* (December 2, 2013). | 1969–1985 IMP hardware evolution, early 1970 5-node ARPANET topology (UCLA, SRI, UCSB, Utah, BBN) with universal symmetry & BFS shortest-path connectivity proofs, McQuillan/Kahn reassembly buffer reservation lockup prevention, exact rational modem line throughput window monitor, and 1973 IMP 3050 OCR + Midas closed-loop verification. |
| **`ColdWarDefense/SkipjackKEA.lean`** | **NSA SKIPJACK & KEA Cryptographic Suite** (1998) | NSA / NIST, *SKIPJACK and KEA Algorithm Specifications, Version 2.0* (29 May 1998). | Bit-exact 256-byte F-table bijection proof, 4-round Feistel G-permutation & Rules A/B universal invertibility (`skipjack_decrypt_encrypt`), FIPS-81 CBC-64 universal invertibility, Annex A test vector verification, KEA Diffie-Hellman exponent symmetry, and Annex B & C 80-bit key derivation proofs. |

---

## Apollo Mission (Apollo 11 AGC — Comanche 055 & Luminary 1A)

The Apollo Mission verification suite spans both the **Command Module (Comanche 055 / Colossus 2A)** core operating system (`ApolloMission/AGCBlockTwoReplication.lean`, `ApolloMission/executive_agc.lean`, `ApolloMission/interpreter_agc.lean`) and the **Lunar Module (Luminary 1A, Build 099)** flight guidance & lunar landing modules in [`ApolloMission/`](ApolloMission/):

* **[`ApolloMission/LEM_GEOMETRY.lean`](ApolloMission/LEM_GEOMETRY.lean)** (`LEM_GEOMETRY.agc`, pp. 320–325):
  * `svdwn2_noop_when_avemidsw_false`, `svdwn1_svdwn2_same_kinematics`, `svdwn2_lunar_b27_to_b29_exact`: Exact `AVEMIDSW` gating and `X2`-indexed B-27/B-5 $\to$ B-29/B-7 scaling conservation.
  * `cdu_roundtrip_exact`: Universal 15-bit `CDULOGIC (1STO2S w) = w` roundtrip for all $w \neq -0$.
  * `rrangleModeSwap_spec` & `dxch_three_step_swap_exact`: Exact `RADMODES`/`ANTENBIT` Mode 1 $\leftrightarrow$ Mode 2 swapping.
  * `rrnb_mode1_eq_mode2` & `rrnb_unit_norm_sq`: Exact algebraic proof that Mode 1 `(T, S)` and Mode 2 `(180° - T, S + 180°)` yield identical unit Line-of-Sight vectors with $\|u\|^2 = 1$ over any commutative ring.
* **[`ApolloMission/PLANETARY_INERTIAL_ORIENTATION.lean`](ApolloMission/PLANETARY_INERTIAL_ORIENTATION.lean)** (`PLANETARY_INERTIAL_ORIENTATION.agc`, pp. 1140–1148):
  * `moonMX_eq_euler_product`: Proves Luminary 1A's `MOONMX(B, F, NODI, I)` equals the exact Euler-angle product $R_z(F + \pi) \cdot R_x(-I) \cdot R_z(\text{NODI}) \cdot R_x(B)$.
  * `earthMX_is_SO3` & `moonMX_is_SO3`: Universal proofs that both `EARTHMX` and `MOONMX` satisfy $MM^\top = I_3$, $M^\top M = I_3$, and $\det(M) = 1$.
  * `rToRp_rpToR_second_order_residual` & `rpToR_rToRp_second_order_residual`: Universal first-order libration cancellation $\text{R-TO-RP}(\text{RP-TO-R}(\mathbf{r}_p)) = \mathbf{r}_p - \mathbf{L}_p \times (\mathbf{L}_p \times \mathbf{r}_p)$ and exact inversion when $\mathbf{L} = 0$.
  * `newangle_tp_split_exact`: Exact algebraic equivalence of Luminary 1A's triple-precision split multiplication (`SL 9D` + `SL* 10D,1` with `SL* 5,1`) across `WEARTH`, `FDOT`, `BDOT`, and `NODDOT`.
* **[`ApolloMission/THE_LUNAR_LANDING.lean`](ApolloMission/THE_LUNAR_LANDING.lean)** (`THE_LUNAR_LANDING.agc`, pp. 785–792):
  * `p63lm_clears_bit14_preserves_other_bits` & `flagorgy_exact_flag_invariant`: Universal `CHAN12` LR Track-Enable bit 14 clearing and 6-flag braking-phase invariants.
  * `ddumcalc_zero_at_target` & `ddumcalc_denominator_pos_safety`: Exact Newton-Raphson convergence at target ignition conditions and strict positive-denominator division-by-zero immunity (`KIGNX/B4 < 0`).
  * `outofpln_zero_in_orbital_plane` & `p63Spot3_antenna_interlock`: Exact orbital-plane orthogonality of `OUTOFPLN` and `CHAN33` bit 6 Landing Radar Position 1 interlock (`CODE500`).
  * `p68_surface_lockout_invariant`, `apollo11_svdwn2_to_p68_scaling_bridge`, & `apollo11_p63_p68_rls_roundtrip`: P68 Tranquility Base abort lockout and cross-module `SVDWN2` $\to$ `VSL2` $\to$ `R-TO-RP` / `P63` $\leftrightarrow$ `P68` landing-site roundtrip theorems.

---

## Selected Mathematical & Architectural Theorems

### 1. Universal Inductive Verification of AGC Block II Erasable Memory (`AGCBlockTwoReplication.lean`)
Rather than relying on brute-force unrolling over the AGC scratchpad (`0o061` through `0o1373`), `eraschkLoop` is verified for arbitrary starting addresses and lengths via structural induction:

$$\forall\,\text{rem}, \text{st}, \text{curr\_addr}, \text{success}, \quad \text{curr\_addr} + \text{rem} \le |\text{st.erasable\_memory}| \implies \text{eraschkLoop}(\text{st}, \text{curr\_addr}, \text{rem}, \text{success}) = (\text{st}, \text{success})$$

This relies on three proved hardware lemmas over `BitVec 16`:
1. `onesComplementAdd_neg_self`: $\forall x \in \text{BitVec } 16,\; \text{onesComplementAdd}(\sim x, x) = \text{0xFFFF}_{16}$
2. `read_write_same`: Immediate read-after-write returns the test pattern.
3. `write_restore_id`: Restoring the original word after destructive bit-pattern testing yields the exact initial `AGCState` record.

### 2. Apollo 11 Executive Priority Multitasking & Self-Check Dispatch (`executive_agc.lean`)
The AGC Executive manages 7 job slots (Core Sets 0–6) prioritized by urgency. When higher-priority jobs enter (e.g. via `FINDVAC`), the Executive suspends the currently running job and context-switches via `CHANG1`. When all core sets are idle (`NEWJOB = -0`), the Executive transfers control to `SELF-CHECK`:
* `ejscan_ccspr_offset_recovery`: Adding `-CCSPR` (`0o67662`) to each `CCS PRIORITY + n*12` instruction word in `EJSCAN` recovers the exact core set offset `n*12` (`12, 24, 36, 48, 60, 72`).
* `add_15_comp15_self`: Universal theorem proving $\forall w \in \text{Word15},\; w + \sim w = -0$ (`0o77777`) in ones'-complement arithmetic.
* `verify_step1_novac` through `verify_step6b_endofjob2_and_idle`: 9 sequential kernel-checked theorems modeling multi-job scheduling, priority preemption, sleep/wake cycles, and idle dispatch.

### 2. Dual-Rail Magnetic Amplifier Ternary Half-Adder & ALU Bridge (`Magnetic_Digital_Elements_1964.lean` & `CrossLayerBridge.lean`)
In his 1964 Kiev paper (Page 366, Fig. 10), Brusentsov derives the ternary half-adder from pulse-current magnetic amplifiers using dual-rail encoding $A = a_p - a_n$ and $B = b_p - b_n$ where $(p, n) \in \{(0,0), (1,0), (0,1)\}$:

$$S = A\,\bar{b}_p\,\bar{b}_n + B\,\bar{a}_p\,\bar{a}_n + a_n b_n - a_p b_p, \qquad Q = a_p b_p - a_n b_n$$

Theorem `fig10_brusentsov_half_adder_algebraic_identity` verifies that for all $3 \times 3 = 9$ dual-rail input pairs, the physical circuit equations satisfy the exact balanced ternary arithmetic invariant:

$$3Q + S = A + B \quad \text{with} \quad S, Q \in \{-1, 0, +1\}$$

Furthermore, `CrossLayerBridge.brusentsov_1964_half_adder_eq_setun_1960_adder` proves that encoding `Setun1960.Trit` into dual-rail signals and evaluating the 1964 magnetic amplifier equations is algebraically identical to the 1960 Setun ALU (`Trit.fullAdder a b .zero`).

### 3. Single-Error Correction in Symmetric Ternary Alphabet (`Setun_Minsk22_Dushanbe_1971.lean`)
Rumyantsev and Soliev (1971, Pages 42–52) construct linear error-correcting codes over $\{-1, 0, +1\}$ where the parity-check matrix columns $(k_j^1, k_j^2, k_j^3)$ represent the balanced ternary coordinates of position $j \in \{1..11\}$. Given a received 11-trit word $X'$, the syndrome is:

$$\sigma_i = \left(\sum_{j=1}^{11} k_j^i X'_j\right) \bmod_{\text{sym}} 3, \qquad \sigma = \sigma_1 + 3\sigma_2 + 9\sigma_3$$

Unlike binary Hamming codes (which only locate the error position), a symmetric ternary channel can experience $+1$ or $-1$ transitions. The decoder simultaneously locates the corrupted trit and determines the restorative delta:

$$N = |\sigma|, \qquad \Delta_N = -\text{sign}(\sigma)$$

Theorem `single_error_correction_all_11_positions` proves that for every position $j \in \{1..11\}$ and every non-zero corruption in $\{-1, 0, +1\}$, `decodeAndCorrect11` recovers the exact transmitted codeword.

### 4. Setun-70 Privilege Architecture & Interrupt Vectoring (`Setun70_1971.lean`)
Setun-70 implements hardware-enforced structured programming (EDS) using a 3-state operating mode trit $c_1 \in \{-1\text{ (user)}, 0\text{ (macro)}, +1\text{ (interrupt)}\}$, two-level status saving in $c[1:32]$, and dual shadow stack pointers $p[1:5] \leftrightarrow p[6:10]$. The formalization verifies:
* `c_frame_roundtrip_verified`: Lossless 12-trit packing and unpacking of $(c_1, c_h, c_a)$ across `IR`, `MACRO`, and `S14 (RETNMC)`.
* `user_mode_spec_triggers_w_minus_28`: Executing a privileged `SPEC` syllable in user mode ($c_1 = -1$) traps to the interrupt handler on ROM page $c_h = 13, c_a = -13$ with cause $w = -28$.
* `macro_in_macro_mode_triggers_w_minus_28`: Nested `MACRO` invocation when $c_1 = 0$ traps with $w = -28$.

### 5. LAPACK DGESV Exact Matrix Solver & Invariant Preservation (`DGESV.lean`)
DGESV solves general linear systems $AX = B$ using LU factorization with partial row pivoting ($P A = L U$). The formalization models the full Fortran 77 LAPACK calling stack in exact arithmetic over `Rat`:
* `dgesv_illegal_n`, `dgesv_illegal_nrhs`, `dgesv_illegal_lda`, `dgesv_illegal_ldb`: Exact negative info parameter guards.
* `dgesv_singular_propagates_info`: Verified propagation of singular matrix flags ($U_{k,k} = 0$) directly to the user info return.
* `dgesv_2x2_exact_solution`: Exact solution of 2x2 systems in $\mathbb{Q}$ verified through `rfl`.

### 6. TempleOS Compression Bound Verification & Kernel Semantics (`TempleOS.lean`)
Formalizes Terry Davis's 64-bit operating system core, including the CArcCompress variable-bit LZW engine (`expand_buf`):
* `unpackU16LE_packU16LE` & `unpackU64LE_packU64LE`: BitVec roundtrip preservation lemmas verified with `bv_decide`.
* `lzwOuterLoop_size_le`: Proves that the decompressor output never exceeds the header's declared `expanded_size` bound:

$$\forall \text{st},\; (\text{lzwOuterLoop st}).\text{out.size} \le \text{st.expanded\_size}$$

---

## Building and Running the Verification Suite

### Prerequisites
* [Lean 4](https://leanprover.github.io/lean4/doc/quickstart.html) (via `elan`)

### Build All Proofs
Clone the repository and run Lake to check all definitions and theorems in the Lean 4 kernel:

```bash
lake build
```

### Execute Hardware Test Benches
You can run the executable self-tests for the Apollo Guidance Computer and the Intel 4004 directly via Lean's interpreter:

```bash
lean --run ApolloMission/AGCBlockTwoReplication.lean
lean --run Intel4004/intel4004.lean
```

**Sample Output (`intel4004.lean`):**
```text
=== Intel 4004 Complete Hardware Replication Verification ===
Executed 29 Machine Cycles (232 Clock Periods)
Active RAM Bank: 2 (CM-RAM pins = 4)
RAM[Bank 2][Chip 1][Reg 1][Char 3] = 9
STATUS[Bank 2][Chip 1][Reg 1][0]   = 7
BCD 9 + 8 Result (R3:R2)           = 17
Subroutine Return Value (R4)       = 0xC
KBP(0b0100) Output (R5)            = 3
Typical I_DD at 25°C, V_DD=-15.0V  = 27.80 mA
All 46 instructions and hardware invariants verified with zero errors.
```

---

## License

Licensed under the Apache License, Version 2.0 (see [`LICENSE`](LICENSE)).
