# fyp_scheduling_algorithms

Lean 4 + Mathlib formalisation of CPU scheduling (FCFS, SJF, SRTF, RR, RMS, DM, EDF).
`GLOSSARY.md` explains the terms and points to their definitions; read it before working on
the proofs. Build with `lake build`.

## Naming conventions

- Names say literally what a definition checks; long names are fine (lines wrap at 100).
- No "online": a policy that reads the whole state is a *state-select* policy
  (`stepNonPreemptiveStateSelect`, `runStateSelect`); jobs all present at time 0 are
  `AllArrivalsAtZero` ("batch" only in prose and the glossary).
- Put the quantifier in the name: good properties say `…AtEvery…`
  (`ShortestAtEveryDispatchRun`), bad ones `…AtSome…` (`HasConvoyEffectAtSomeDispatch`).
- Give each negation its own name and an iff with `¬` (`IsOptimalOverSteps` /
  `IsBeatenOverSteps`, `not_isOptimalOverSteps_iff`).
