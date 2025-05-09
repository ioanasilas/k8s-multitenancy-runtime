package k8s.monitoring.tla;

import java.io.*;
import java.util.Random;

public class TenantLoadSimulator {

    static String[] tenants = {"tenant1", "tenant2"};

    public static void main(String[] args) throws Exception {
        if (args.length != 1 ||
                (!args[0].equals("violation") && !args[0].equals("noviolation"))) {
            System.out.println("Usage: java ContinuousPodGenerator <violation|noviolation>");
            return;
        }

        boolean addViolation = args[0].equals("violation");
        String mode = addViolation ? "with violation" : "no violation";
        System.out.println("Running in mode: " + mode + ". Generating pods continuously...");

        // ensure namespaces exist
        for (String tenant : tenants) {
            System.out.println("Ensuring namespace exists: " + tenant);
            runCommand("kubectl create namespace " + tenant + " --dry-run=client -o yaml | kubectl apply -f -");
        }

        Random rand = new Random();
        int counter = 1;

        while (true) {
            System.out.printf("\n--- Pod cycle %d ---\n", counter);

            // tenant1 pod
            String podName1 = "t1-auto-pod" + counter;
            createPod("tenant1", podName1, "k8s-worker1");

            // tenant2 pod (violation 10% of the time)
            String podName2 = "t2-auto-pod" + counter;
            boolean isViolation = addViolation && rand.nextDouble() < 0.1;

            if (isViolation) {
                System.out.println("Adding violation pod: " + podName2 + " (tenant2 on worker1)");
                createPod("tenant2", podName2, "k8s-worker1");
            } else {
                createPod("tenant2", podName2, "k8s-worker2");
            }
            counter++;
        }
    }

    static void createPod(String tenant, String podName, String nodeName) throws Exception {
        String cmd = String.format(
                "kubectl run %s --image=k8s.gcr.io/pause:3.9 --restart=Never -n %s --labels=generator=auto --overrides='{ " +
                        "\"apiVersion\": \"v1\", " +
                        "\"spec\": { \"nodeSelector\": { \"kubernetes.io/hostname\": \"%s\" } } }'",
                podName, tenant, nodeName
        );
        System.out.println("Creating pod: " + podName + " in namespace: " + tenant + " on node: " + nodeName);
        runCommand(cmd);
    }

    static void runCommand(String command) throws Exception {
        ProcessBuilder builder = new ProcessBuilder("bash", "-c", command);
        Process process = builder.start();
        BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
        String line;
        while ((line = reader.readLine()) != null) {
            System.out.println(line);
        }
        process.waitFor();
    }
}
