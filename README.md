# Kubernetes Multi-Tenancy Runtime Verification

This project tests **runtime verification for Kubernetes multi-tenancy** using TLA+ and Kubernetes audit logs. The idea is to monitor what’s happening in the cluster and check that tenants don't step over each other (for example, pods only get scheduled on their own nodes).

---

## Files

- `alerts/`: logs of detected violations (in JSON, one per line)
- `logs/`: sample Kubernetes audit logs (violation + no-violation cases)
- `run_results/`: CSVs tracking TLC runs (times + if violations were found)
- `tla_specs/`: the TLA+ specs:
  - `NodeIsolationSystem.tla`: defines the **expected system behavior**
  - `node_isolation.tla`: trace-checking spec for **runtime verification**
  - `Json.tla`: helper module for parsing JSON logs
- `java/`: simple Java runner scripts:
  - `SplitThenRun.java`: splits audit logs into batches and runs TLC for each
  - `TenantLoadSimulator.java`: (if included) simulates tenants for testing
- `cluster-audit-policy.yaml`: audit policy to capture **create/update/delete** events
- `fluent-bit-config.conf`: example config to filter audit logs with Fluent Bit
- `pom.xml`: Java build config (Maven)

---

## How it works

1. **Logs**: We collect Kubernetes audit logs (in this case pod creation across tenants).
2. **Specs**: TLA+ specs define what should/shouldn’t happen (like: tenant1’s pod shouldn't land on tenant2’s node).
3. **Runtime checking**: 
   - Logs are split into batches.
   - TLC runs on each batch to check if the invariant holds.
   - Alerts + timings are logged.

---

## 🛠 Running it

- **Build Java:**  
  Run `mvn package` to compile the Java runner.

- **Run the checker:**  
  Example usage (adjust paths as needed):

  ```bash
  java -cp target/k8s-monitoring-tla-1.0-SNAPSHOT.jar:/path/to/tla2tools.jar \
    k8s.monitoring.tla.SplitThenRun \
    /path/to/logs/node_isolation_violation.json \
    /path/to/tla_specs/node_isolation.tla \
    /path/to/node_isolation.cfg \
    /path/to/alloc.json \
    /path/to/tla2tools.jar
  ```

- **Output:**
  - Results go to `run_results/`
  - Alerts (if any) are written in `alerts/`

---

## What this shows

- How fast TLC can process different batch sizes (timing results in CSVs)
- That the TLA+ spec **detects violations** (example logs included)
- Example setup that could be expanded for **real-time Kubernetes monitoring**

---

## Relevance

- Uses **formal methods (TLA+)** to check **real-world Kubernetes logs**
- Tests **multi-tenancy isolation** at runtime (e.g., tenant boundaries)
- Can be expanded into a continuous monitoring tool

---
