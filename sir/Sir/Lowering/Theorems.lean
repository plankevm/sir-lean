import Sir.Lowering.Proofs.Program

namespace Sir

theorem Lowering.ProgramSchedule.equiv (schedule : Lowering.ProgramSchedule) :
    schedule.check = .ok () → Lowering.Equiv schedule.vars schedule.stack :=
  Lowering.Proofs.ProgramSchedule.equiv schedule

theorem Lowering.StackSchedule.equiv (schedule : Lowering.StackSchedule) :
    schedule.check = .ok () →
      Lowering.Equiv schedule.program.vars schedule.program.stack :=
  Lowering.Proofs.StackSchedule.equiv schedule

theorem Lowering.Scheduler.Accepted.equiv
    {scheduler : Lowering.Scheduler} (accepted : scheduler.Accepted)
    {statements : Array Vars.Stmt} {schedule : Lowering.StackSchedule}
    (produced : scheduler statements = .ok schedule) :
    Lowering.Equiv schedule.program.vars schedule.program.stack :=
  Lowering.Proofs.Scheduler.Accepted.equiv accepted produced

theorem Lowering.Scheduler.Accepted.schedules_input
    {scheduler : Lowering.Scheduler} (accepted : scheduler.Accepted)
    {statements : Array Vars.Stmt} {schedule : Lowering.StackSchedule}
    (produced : scheduler statements = .ok schedule) :
    schedule.entry.vars.statements = statements :=
  Lowering.Proofs.Scheduler.Accepted.schedules_input accepted produced

theorem Lowering.spillAll_accepted : Lowering.spillAll.Accepted :=
  Lowering.Proofs.spillAll_accepted

end Sir
