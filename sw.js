// Loop service worker: app shell cached on install, Esri tiles cached as they are seen (so a hole viewed once works offline).
const SHELL = "loop-shell-v202610061600"; const TILES = "loop-tiles-v1";
const SHELL_FILES = ["./", "./index.html", "./engine.js", "./data.js", "./manifest.webmanifest", "./icon-192.png", "./icon-512.png"];
self.addEventListener("install", e => { e.waitUntil(caches.open(SHELL).then(c => c.addAll(SHELL_FILES)).then(() => self.skipWaiting())); });
self.addEventListener("activate", e => { e.waitUntil(caches.keys().then(ks => Promise.all(ks.filter(k => k.startsWith("loop-shell-") && k !== SHELL).map(k => caches.delete(k)))).then(() => self.clients.claim())); });
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
