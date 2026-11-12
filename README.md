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
| **`Setun_1960.lean`** | **MSU Setun** (1960) | N. P. Brusentsov, *Вычислительная машина «Сетунь» Московского государственного университета*, Kiev Symposium on Cybernetics, pp. 226–233 (1960). | Balanced ternary alphabet $\{-1, 0, +1\}$, 3-input serial full adder with single carry flip-flop, 18-trit fixed-point scaling ($3^{16} = 43,046,721$), 5th-trit addressing modes (`fullWord`, `seniorHalfWord`, `juniorHalfWord`), dual condition flags ($\omega_+$ and $\omega_\gamma$), all 24 Table 1 opcodes, drum/RAM zone transfers, and Page 226 Author's Errata cycle timings ($325\,\mu\text{s}$ multiplication). |
| **`Magnetic_Digital_Elements_1964.lean`** | **Pulse-Current Magnetic Amplifiers & Ferrite Laddics** (1964) | *Магнитные элементы автоматики, телемеханики, измерительной и вычислительной техники*, Naukova Dumka, Kiev, pp. 285–291, 361–366, 480–487 (1964). | **1. Olshvang**: Core testing equations ($\Delta B, H_y$) and dual connector windings ($w_p = 24, w_y = 14$).<br>**2. Brusentsov**: Pulse-current magnetic amplifier gates (`magInhibit`, `magAnd`, `magOr`), the 6 electrical fan-out/interconnection rules, 2-bit binary decoder (Fig. 7), dual-rail mutual-inhibition ternary cell (Fig. 8), 2-trit 9-output ternary decoder (Fig. 9), and the ternary half-adder algebraic identity $3Q + S = A + B$ (Fig. 10).<br>**3. Nezhivov & Ryabinin**: 14-rung ferrite ladder (`лесенка` / Laddic) Boolean product-of-sums, blocking factor $K_b = \frac{m + 2(N-n)L}{2m + 2(N-1)L}$, and $\text{MMF}$ equivalence $M_n = K_b M_1$.<br>**4. Chinaev**: Extremal regulator quadratic functional $Q = \sum (\Delta x_i)^2 \ge 0$. |
| **`AGCBlockTwoReplication.lean`** | **Apollo Guidance Computer Block II** (1969) | MIT Instrumentation Lab, *Comanche 055 (Colossus 2A)*, `AGC_BLOCK_TWO_SELF-CHECK.agc`. | Native `BitVec 16` 1's complement hardware arithmetic with end-around carry (`onesComplementAdd`), Erasable/Fixed Core Rope memory state, and `ERASCHK`, `CNTRCHK`, `CYCLSHFT`, and `BNKCHK` self-check routines. Features a **universal structural induction proof** (`eraschkLoop_universal_correct`) proving non-destructive scratchpad verification over arbitrary address ranges in $O(1)$ kernel steps without loop unrolling. |
| **`executive_agc.lean`** | **Apollo Guidance Computer (Executive Routine)** (1969) | MIT Instrumentation Lab, *Comanche 055 (Colossus 2A)*, `EXECUTIVE.agc`, pp. 1208–1220. | Complete priority-based cooperative job scheduler for the AGC Block II: 15-bit ones'-complement arithmetic, hardware registers (`A`, `L`, `Q`, `EBANK`, `FBANK`, `BBANK`, `Z`), 7 Core Sets (`0..6`), VAC area allocation (`VAC1..VAC5`), `-CCSPR` instruction word offset recovery, `NOVAC`, `FINDVAC`, `CHANG1` context switching, `PRIOCHNG`, `JOBSLEEP`, `JOBWAKE`, `ENDOFJOB`, and dispatch to `SELFCHK`. Includes 9 kernel-verified step theorems. |
| **`interpreter_agc.lean`** | **Apollo Guidance Computer (Interpretive Language Engine)** (1969) | MIT Instrumentation Lab, *Comanche 055 (Colossus 2A)*, `INTERPRETER.agc`, pp. 1107–1199. | Complete formal specification of Hal Laning's AGC Polish-notation bytecode virtual machine: multi-precision fixed-point vector and matrix arithmetic, editing registers (`CYR`, `SR`, `CYL`, `EDOP`), bank-switching (`SUPERBNK`), double-precision multiply (`DMPSUB`), rounding (`ROUNDSUB`), and kernel-verified execution proofs. |
| **`Setun70_1971.lean`** | **Setun-70 Two-Stack EDS Architecture** (1971) | N. P. Brusentsov & E. A. Zhogolev, *Структура и алгоритм функционирования малой вычислительной машины «Сетунь-70»*, Vychislitel'naya Tekhnika i Voprosy Kibernetiki, Vol. 8, LGU, pp. 34–51 (1971). | Complete ALGOL-60 hardware specification translated to Lean 4: 6-trit syllables ($3^6 = 729$, $[-364..+364]$), 18-trit 3-syllable words, 27 Level-1 pages (9 RAM, 18 ROM) $\times$ 81 syllables, Level-2 page memory $f[-1:1, -3280:3280, -40:40]$, all 27 Basic RPN operations (`B1..B27`), all 27 Special/Privileged operations (`S1..S27`), `REFSYL`, `MACRO`, `INCRC`, and the 13 hardware interrupt vectors $w \in \{-40..-28\}$. |
| **`Setun_Minsk22_Dushanbe_1971.lean`** | **Symmetric Ternary Hamming Codes, BVP & CPM Scheduling** (1971) | Ed. I. U. Soliev, *Вопросы технического и математического обеспечения ЭЦВМ «Сетунь» и «Минск-22»*, Tajik State University, Dushanbe, pp. 1–112 (1971). | **Ch. 1–2 (Soliev)**: TGU Setun 1965–1970 utilization reconciliation and magnetic amplifier thermal/noise thresholds ($+10^\circ\text{C}..+70^\circ\text{C}$, $20\%$ noise rejection, $80\%$ regeneration).<br>**Ch. 3 (Yukhanonov)**: Linear conjugation boundary value problem, Noether-Mikhailov index identity $l - p = 2\kappa$, and contraction mapping series.<br>**Ch. 4 (Rumyantsev & Soliev)**: Symmetric ternary Hamming codes over $\{-1, 0, +1\}$, sphere-packing bound $3^m \ge 2(m+n)+1$, syndrome locator $N = |\sigma|$, error corrector $\Delta_N = -\text{sign}(\sigma)$, and exhaustive verification of the $(11, 8)$ code across all 11 positions.<br>**Ch. 8–9 (Kurtakov)**: Fixed-point linear system solver $x_{n+1} = \alpha x_n + \beta$ and 18-trit packed Critical Path Method (CPM) scheduler ($T_i^{(0)}, T_i^{(1)}, R_{i,j}, r_{i,j}$) verified on the 10-event network graph. |
| **`intel4004.lean`** | **Intel 4004 MCS-4 Microprocessor** (1971) | Intel Corporation, *MCS-4/40 Component Data Catalog: 4004 Single Chip 4-Bit P-Channel Microprocessor*, pp. 8-15 to 8-23 (1971). | Complete 4-bit CPU, 16 index registers ($R_0..R_{15}$ / pairs $P_0..P_7$), 4-level 12-bit address stack, `CM-RAM0..3` bank decoder (`DCL`), `SRC` latch, 8$\times$4$\times$4$\times$16 RAM main & status arrays, all 46 instructions (256-byte opcode table), $I_{DD}$ temperature/voltage model, and a kernel-proved 29-cycle (232-clock) machine-code execution suite. |
| **`CrossLayerBridge.lean`** | **1964 Physics $\leftrightarrow$ 1960 ALU Isomorphism** | Cross-module formal bridge (`Magnetic_Digital_Elements_1964` $\to$ `Setun_1960`). | Proves (`brusentsov_1964_half_adder_eq_setun_1960_adder`) that Brusentsov's 1964 dual-rail pulse-current magnetic amplifier half-adder equations compute the exact same `(sum, carry_out)` values as the 1960 Setun serial full-adder (`Trit.fullAdder a b .zero`). |
| **`DGESV.lean`** | **Netlib LAPACK General Linear Solver** (1992) | Netlib LAPACK 3.x, `dgesv.f`, `dgetrf.f`, `dgetf2.f`, `dgetrs.f`, `dlaswp.f`, `dtrsm.f`. | Complete zero-axiom, zero-sorry formalization of LAPACK general linear system solver $AX = B$ over exact arithmetic (`Rat` / generic `LAPACKField`). Transcribes full Fortran 77 dependency tree with explicit 1-based indexing, partial pivoting, permutation composition, triangular back-substitution, parameter validation theorems (`dgesv_illegal_n`, etc.), and singular matrix propagation. |
| **`TempleOS.lean`** | **TempleOS Operating System Core** (2013) | Terry A. Davis, *TempleOS Version 5.03*, `Kernel/Dsk/DskStrA.HC`, `Kernel/Compress.HC`, `Compiler/`. | Complete zero-axiom formalization of TempleOS 64-bit architecture: RedSea 64-bit filesystem directory records and cluster allocators, CArcCompress LZW decompressor (`expand_buf`) with verified universal output bounds (`lzwOuterLoop_size_le`), and HolyC operator precedence parser with Pratt precedence binding. |

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
lean --run AGCBlockTwoReplication.lean
lean --run intel4004.lean
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
