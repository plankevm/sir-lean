import Sir.Lowering.Proofs.Headline

namespace Sir

theorem Lowering.StackSchedule.equiv (schedule : Lowering.StackSchedule)
    (accepted : schedule.check = .ok ()) :
    Lowering.Equiv schedule.vars schedule.stack :=
  Lowering.Proofs.StackSchedule.equiv schedule accepted

theorem Lowering.Scheduler.Accepted.equiv
    {scheduler : Lowering.Scheduler} (accepted : scheduler.Accepted)
    {statements : Array Vars.Stmt} {schedule : Lowering.StackSchedule}
    (produced : scheduler statements = .ok schedule) :
    Lowering.Equiv schedule.vars schedule.stack :=
  schedule.equiv (accepted statements schedule produced).2

theorem Lowering.spillAll_accepted : Lowering.spillAll.Accepted :=
  Lowering.Proofs.spillAll_accepted

end Sir
