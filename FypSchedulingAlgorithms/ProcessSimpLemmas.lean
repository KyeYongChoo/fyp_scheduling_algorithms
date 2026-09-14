import FypSchedulingAlgorithms.Process
namespace AperiodicProcess

@[simp]
theorem process_id (p : AperiodicProcess) :
    Process.id p = p.id := by
  rfl

@[simp]
theorem process_arrival (p : AperiodicProcess) :
    Process.arrival p = p.arrival := by
  rfl

@[simp]
theorem process_remaining (p : AperiodicProcess) :
    Process.remaining p = p.remaining := by
  rfl

@[simp]
theorem process_burst (p : AperiodicProcess) :
    Process.burst p = p.burst := by
  rfl

@[simp]
theorem process_tick (p : AperiodicProcess) :
    Process.tick p = { p with remaining := p.remaining - 1 } := by
  rfl

attribute [simp] Process.id_invariant_wrt_tick
attribute [simp] Process.arrival_invariant_wrt_tick

end AperiodicProcess



namespace PeriodicProcess

@[simp]
theorem process_id (p : AperiodicProcess) :
    Process.id p = p.id := by
  rfl

@[simp]
theorem process_arrival (p : AperiodicProcess) :
    Process.arrival p = p.arrival := by
  rfl

@[simp]
theorem process_remaining (p : AperiodicProcess) :
    Process.remaining p = p.remaining := by
  rfl

@[simp]
theorem process_burst (p : AperiodicProcess) :
    Process.burst p = p.burst := by
  rfl

@[simp]
theorem process_tick (p : AperiodicProcess) :
    Process.tick p = { p with remaining := p.remaining - 1 } := by
  rfl

attribute [simp] Process.id_invariant_wrt_tick
attribute [simp] Process.arrival_invariant_wrt_tick

end PeriodicProcess
