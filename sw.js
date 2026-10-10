// Loop service worker: app shell cached on install, Esri tiles cached as they are seen (so a hole viewed once works offline).
// SHELL is a hash of the page, the engine and the data: any rebuild changes this file, the browser installs the new worker, it caches the new
// shell, drops the old one, takes over the open pages and reloads them (an update, never a first install, has old shell caches to drop).
const SHELL = "loop-shell-e2017b620f"; const TILES = "loop-tiles-v1";
const SHELL_FILES = ["./", "./index.html", "./engine.js", "./ledger.js", "./swing.js", "./data.js", "./manifest.webmanifest", "./icon-192.png", "./icon-512.png"];
self.addEventListener("install", e => { e.waitUntil(caches.open(SHELL).then(c => c.addAll(SHELL_FILES)).then(() => self.skipWaiting())); });
self.addEventListener("activate", e => { e.waitUntil((async () => {
  const old = (await caches.keys()).filter(k => k.startsWith("loop-shell-") && k !== SHELL);
  await Promise.all(old.map(k => caches.delete(k)));
  await self.clients.claim();
  if (!old.length) return;   // a first install: nothing was showing the previous version
  const cs = await self.clients.matchAll({ type: "window", includeUncontrolled: true });
  // after activation has completed (a navigation awaited inside it would wait for this worker's fetch handler, which waits for activation)
  setTimeout(() => cs.forEach(c => { const msg = () => { try { c.postMessage({ type: "loop-reload" }); } catch (err) {} };
    try { c.navigate(c.url).catch(msg); } catch (err) { msg(); } }), 50);
})()); });
self.addEventListener("fetch", e => {
  const url = new URL(e.request.url);
  if (url.hostname.endsWith("arcgisonline.com")) {
    e.respondWith(caches.open(TILES).then(async c => { const hit = await c.match(e.request); if (hit) return hit; try { const r = await fetch(e.request); if (r.ok) c.put(e.request, r.clone()); return r; } catch (err) { return hit || Response.error(); } }));
    return;
  }
  if (url.origin === location.origin) {
    e.respondWith(caches.match(e.request).then(hit => hit || fetch(e.request).then(r => { if (r.ok && e.request.method === "GET") caches.open(SHELL).then(c => c.put(e.request, r.clone())); return r; })));
  }
});
