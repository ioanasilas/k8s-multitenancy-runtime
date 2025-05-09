package k8s.monitoring.tla;

import java.io.*;
import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.List;

public class SplitThenRun {
    public static void main(String[] args) throws Exception {
        if (args.length != 5 && args.length != 6) {
            System.out.println("wrong number of arguments");
            System.out.println("""
usage:
  java -cp target/k8s-monitoring-tla-1.0-SNAPSHOT.jar:/path/to/tla2tools.jar k8s.monitoring.tla.SplitThenRun \\
      /absolute/path/to/input.json \\
      /absolute/path/to/spec.tla \\
      /absolute/path/to/template.cfg \\
      /absolute/path/to/alloc.json \\
      /absolute/path/to/tla2tools.jar \\
      [checkIntervalSeconds]
""");
            System.exit(1);
        }

        String inputFile = args[0];
        String specFile = args[1];
        String cfgFile = args[2];
        String allocFile = args[3];
        String tlaToolsPath = args[4];

        // optional: check interval
        int checkIntervalSeconds = 2;
        if (args.length == 6) {
            checkIntervalSeconds = Integer.parseInt(args[5]);
        }
        System.out.println("check interval set to " + checkIntervalSeconds + " seconds.");

        // batch sizes (how many logs total to process per batchSize)
        int[] batchSizes = {10, 100, 100, 1000, 1000};

        // how many logs to read per loop (small chunks)
        int[] logsPerReadArr = {10, 10, 50, 100, 500};

        // create /tmp dir for batches
        File tmpDir = new File("/tmp/node_isolation_batches");
        if (!tmpDir.exists()) {
            tmpDir.mkdirs();
            System.out.println("created temporary batch directory: " + tmpDir.getAbsolutePath());
        }

        // make sure alloc.json exists
        File alloc = new File(allocFile);
        if (!alloc.exists()) {
            alloc.getParentFile().mkdirs();
            try (BufferedWriter writer = new BufferedWriter(new FileWriter(alloc))) {
                writer.write("{}");
            }
            System.out.println("created empty alloc file at: " + alloc.getAbsolutePath());
        }

        // alerts log file
        File alertsLog = new File("alerts_detected.json");
        if (!alertsLog.exists()) {
            try (BufferedWriter writer = new BufferedWriter(new FileWriter(alertsLog))) {
                // empty ndjson
            }
            System.out.println("created alerts log at: " + alertsLog.getAbsolutePath());
        }

        // csv to track tlc runtimes
        String csvFile = "tlc_run_results.csv";
        boolean csvExists = new File(csvFile).exists();
        PrintWriter csvWriter = new PrintWriter(new FileWriter(csvFile, true));
        if (!csvExists) {
            csvWriter.println("BatchNumber,BatchSize,DurationMillis,ExitCode");
        }

        int lastReadLine = 0;

        // loop over each batchSize
        for (int i = 0; i < batchSizes.length; i++) {
            int batchSize = batchSizes[i];
            int logsPerRead = logsPerReadArr[i];

            System.out.printf("\n=== starting batchSize %d (want to process %d logs total), logsPerRead: %d ===\n",
                    batchSize, batchSize, logsPerRead);

            int batchNumber = 1;
            long totalTlcTimeMillis = 0;
            int totalLogsProcessed = 0;

            // keep going until we process batchSize logs total
            while (totalLogsProcessed < batchSize) {
                List<String> newLines = readNextLines(inputFile, lastReadLine, logsPerRead);
                if (newLines.isEmpty()) {
                    System.out.println("no new logs found. waiting...");
                    Thread.sleep(checkIntervalSeconds * 1000L);
                    continue;
                }

                String batchFile = "/tmp/node_isolation_batches/node_isolation_batch_" + batchSize + "_" + batchNumber + ".json";
                writeLinesToFile(batchFile, newLines);

                String batchCfgFile = "/tmp/node_isolation_batches/node_isolation_batch_" + batchSize + "_" + batchNumber + ".cfg";
                generateBatchCfg(cfgFile, batchCfgFile, batchFile, allocFile);

                lastReadLine += newLines.size();
                totalLogsProcessed += newLines.size();

                System.out.println("starting tlc for batchSize " + batchSize + " run " + batchNumber + "...");
                Instant start = Instant.now();
                int exitCode = runTLC(specFile, batchCfgFile, tlaToolsPath);
                Instant end = Instant.now();
                long tlcDurationMillis = Duration.between(start, end).toMillis();
                System.out.println("tlc for batchSize " + batchSize + " run " + batchNumber + " took " + tlcDurationMillis + " ms");

                csvWriter.printf("%d_%d,%d,%d,%d%n", batchSize, batchNumber, batchSize, tlcDurationMillis, exitCode);
                csvWriter.flush();

                totalTlcTimeMillis += tlcDurationMillis;

                if (exitCode != 0) {
                    System.out.println(">>> alert detected in batchSize " + batchSize + " run " + batchNumber + " (exit code: " + exitCode + ")");
                    try (FileWriter fw = new FileWriter(alertsLog, true);
                         BufferedWriter bw = new BufferedWriter(fw);
                         PrintWriter out = new PrintWriter(bw)) {

                        String timestamp = Instant.now().toString();
                        out.printf(
                                "{ \"batchNumber\": %d, \"batchSize\": %d, \"batchFile\": \"%s\", \"cfgFile\": \"%s\", \"detectedAt\": \"%s\", \"exitCode\": %d, \"tlcDurationMillis\": %d }%n",
                                batchNumber, batchSize, batchFile, batchCfgFile, timestamp, exitCode, tlcDurationMillis
                        );
                    }
                } else {
                    System.out.println("no alert detected in batchSize " + batchSize + " run " + batchNumber);
                }

                batchNumber++;
            }

            double average = (double) totalTlcTimeMillis / (batchNumber - 1);
            csvWriter.printf("AVERAGE_FOR_BATCHSIZE_%d,%.2f,%d%n", batchSize, average, (batchNumber - 1));
            csvWriter.flush();
            System.out.printf("average tlc runtime for batchSize %d: %.2f ms over %d batches\n", batchSize, average, (batchNumber - 1));
        }

        csvWriter.close();
        System.out.println("\n all batch sizes completed!");
    }

    // reads up to maxLines starting after skipLines
    static List<String> readNextLines(String filePath, int skipLines, int maxLines) throws IOException {
        List<String> lines = new ArrayList<>();
        try (BufferedReader br = new BufferedReader(new FileReader(filePath))) {
            for (int i = 0; i < skipLines; i++) {
                br.readLine(); // skip old lines
            }
            String line;
            for (int i = 0; i < maxLines && (line = br.readLine()) != null; i++) {
                lines.add(line);
            }
        }
        return lines;
    }

    // writes a list of lines to a file
    static void writeLinesToFile(String filePath, List<String> lines) throws IOException {
        try (BufferedWriter bw = new BufferedWriter(new FileWriter(filePath))) {
            for (String line : lines) {
                bw.write(line);
                bw.newLine();
            }
        }
    }

    // generates a cfg file for the batch based on a template
    static String generateBatchCfg(String templateCfgPath, String outputCfgPath, String logFileName, String allocFileName) throws IOException {
        List<String> lines = new ArrayList<>();
        try (BufferedReader reader = new BufferedReader(new FileReader(templateCfgPath))) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().startsWith("LogFile")) {
                    lines.add("  LogFile = \"" + logFileName + "\"");
                } else if (line.trim().startsWith("AllocFile")) {
                    lines.add("  AllocFile = \"" + allocFileName + "\"");
                } else {
                    lines.add(line);
                }
            }
        }
        try (BufferedWriter writer = new BufferedWriter(new FileWriter(outputCfgPath))) {
            for (String l : lines) {
                writer.write(l);
                writer.newLine();
            }
        }
        return outputCfgPath;
    }

    // runs tlc as a subprocess
    // continue if we do not stop on first violation
    static int runTLC(String specFile, String cfgFile, String tlaToolsPath) throws IOException, InterruptedException {
        ProcessBuilder pb = new ProcessBuilder("java", "-cp", tlaToolsPath, "tlc2.TLC",
                "-continue",
                "-config", new File(cfgFile).getAbsolutePath(),
                new File(specFile).getAbsolutePath());
        pb.inheritIO();  // show tlc output in console
        Process process = pb.start();
        int exitCode = process.waitFor();
        System.out.println("tlc exited with exit code: " + exitCode);
        return exitCode;
    }
}
