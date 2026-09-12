import { QueueConsole } from "@/components/queue-console";

export default function Home() {
  return (
    <main style={{ maxWidth: 1100, margin: "0 auto", padding: "24px 16px" }}>
      <h1 style={{ fontSize: 20, fontWeight: 600, marginBottom: 4 }}>
        Emissary-Archangel-0.0.1
      </h1>
      <p style={{ fontSize: 13, opacity: 0.7, marginBottom: 20 }}>
        Manual, per-theorem translation runs. Nothing here is pushed to
        CompeteMath automatically — every result is stored locally
        (data/queue.json) until you decide otherwise.
      </p>
      <QueueConsole />
    </main>
  );
}
