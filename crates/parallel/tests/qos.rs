//! The pool honours a requested worker scheduling class. Its own process, since
//! the pool is a process-wide singleton and the request only counts before it.

#![cfg(target_os = "linux")]

const SCHED_IDLE: core::ffi::c_int = 5;

unsafe extern "C" {
    fn sched_getscheduler(pid: core::ffi::c_int) -> core::ffi::c_int;
}

fn policy() -> core::ffi::c_int {
    // SAFETY: pid 0 names the calling thread on Linux, and the call only reads.
    unsafe { sched_getscheduler(0) }
}

#[test]
fn requested_utility_workers_run_in_the_idle_class() {
    assert_ne!(policy(), SCHED_IDLE, "the test thread starts in the default class");

    parallel::set_worker_qos(parallel::Qos::Utility);

    let observed: Vec<core::ffi::c_int> = parallel::map_collect(parallel::num_threads(), |_| policy());

    assert!(
        observed.iter().all(|&p| p == SCHED_IDLE),
        "every thread that ran the dispatch is in the idle class: {observed:?}"
    );
    assert_eq!(
        policy(),
        SCHED_IDLE,
        "the dispatching thread joined the class as worker 0"
    );
}
