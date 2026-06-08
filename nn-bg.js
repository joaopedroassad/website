(function () {
  const canvas = document.getElementById('nn-bg');
  if (!canvas) return;
  const ctx = canvas.getContext('2d');

  let w, h;
  let mouseX = -9999, mouseY = -9999;
  const POINTS = 220;
  const LINK_DIST = 170;
  const GLOW_RADIUS = 250;
  const BASE_ALPHA = 0.07;
  const BRIGHT_ALPHA = 0.38;
  let pts = [];
  let frame = 0;

  /* ── Signals ("ideas") ── */
  const signals = [];
  const SIGNAL_PX_SPEED = 2.5;
  const MAX_SIGNALS = 8;
  const SPAWN_INTERVAL = 90;
  const EDGE_MARGIN = 100;
  const MAX_HOPS = 12;
  const TRAIL_FADE = 200;
  let spawnTimer = 0;

  /* ── Search state ── */
  var mode = 'normal'; // normal, waiting, search, fadeout, organize
  var modeTimer = 1200 + Math.floor(Math.random() * 1200);
  var searchType = '';
  var cycleStep = 0; // 0=BFS, 1=DFS, 2=NN
  var searchQueue = [];
  var searchVisited = null;
  var searchParent = null;
  var searchTarget = -1;
  var searchStart = -1;
  var searchTraces = [];
  var searchPathTraces = [];
  var searchStepTimer = 0;
  var searchStartFrame = 0;
  var adjSnapshot = [];
  var SEARCH_STEP_RATE = 10;
  var SEARCH_TRACE_FADE = 600;
  /* ── Organize state ── */
  var organizeLayers = []; // array of arrays of pt indices
  var organizeOrigins = {}; // idx -> {x, y}
  var organizeTargets = {}; // idx -> {x, y}
  var organizePhase = ''; // forming, hold, releasing
  var organizeTimer = 0;
  var ORGANIZE_FORM = 300;
  var ORGANIZE_RELEASE = 150;
  var nnSignals = [];
  var NN_SIGNAL_SPEED = 0.09;
  var nnCurrentLayer = 0;
  var nnHoldPhase = ''; // 'traveling', 'glowing'
  var nnGlowTimer = 0;
  var NN_GLOW_DURATION = 60;
  var nnNodeGlow = {}; // nodeIdx -> intensity (0-1)
  var nnOutputNode = -1; // single lit output node

  function resize() {
    w = canvas.width = window.innerWidth;
    h = canvas.height = window.innerHeight;
  }

  var allPts = [];
  var spawnQueue = [];
  var spawned = null; // Set of indices already in pts
  var SPAWN_PER_FRAME = 2;

  function seed() {
    pts = [];
    allPts = [];
    for (let i = 0; i < POINTS; i++) {
      allPts.push({
        x: Math.random() * w,
        y: Math.random() * h,
        vx: (Math.random() - 0.5) * 0.25,
        vy: (Math.random() - 0.5) * 0.25,
      });
    }
    spawned = new Set();
    spawnQueue = [];
    // Start with one random node
    var start = Math.floor(Math.random() * allPts.length);
    spawnNode(start);
    signals.length = 0;
  }

  function spawnNode(idx) {
    if (spawned.has(idx)) return;
    spawned.add(idx);
    pts.push(allPts[idx]);
    // Find unspawned neighbors and enqueue them
    for (var i = 0; i < allPts.length; i++) {
      if (spawned.has(i)) continue;
      var dx = allPts[idx].x - allPts[i].x;
      var dy = allPts[idx].y - allPts[i].y;
      if (Math.sqrt(dx * dx + dy * dy) < LINK_DIST) {
        if (spawnQueue.indexOf(i) === -1) spawnQueue.push(i);
      }
    }
  }

  function isEdge(idx) {
    var p = pts[idx];
    return p.x < EDGE_MARGIN || p.x > w - EDGE_MARGIN ||
           p.y < EDGE_MARGIN || p.y > h - EDGE_MARGIN;
  }

  function neighbors(idx, exclude) {
    const out = [];
    for (let i = 0; i < pts.length; i++) {
      if (i === idx || i === exclude) continue;
      const dx = pts[idx].x - pts[i].x;
      const dy = pts[idx].y - pts[i].y;
      if (Math.sqrt(dx * dx + dy * dy) < LINK_DIST) out.push(i);
    }
    return out;
  }

  function spawnSignalFrom(fromIdx) {
    var nb = neighbors(fromIdx, -1);
    if (!nb.length) return;
    var to = nb[Math.floor(Math.random() * nb.length)];
    var visited = new Set();
    visited.add(fromIdx);
    signals.push({
      from: fromIdx, to: to, t: 0, hops: 0, alive: true,
      visited: visited,
      trail: [{ idx: fromIdx, frame: frame }]
    });
  }

  function spawnSignal() {
    var edgeNodes = [];
    for (let i = 0; i < pts.length; i++) {
      if (isEdge(i)) edgeNodes.push(i);
    }
    if (!edgeNodes.length) return;
    spawnSignalFrom(edgeNodes[Math.floor(Math.random() * edgeNodes.length)]);
  }

  /* ── Search helpers ── */
  function snapshotAdj() {
    adjSnapshot = [];
    for (var i = 0; i < pts.length; i++) {
      adjSnapshot.push(neighbors(i, -1));
    }
  }

  function bfsFarthest(from) {
    var vis = new Set([from]);
    var queue = [from];
    var last = from;
    while (queue.length) {
      last = queue.shift();
      var nb = adjSnapshot[last];
      for (var j = 0; j < nb.length; j++) {
        if (!vis.has(nb[j])) { vis.add(nb[j]); queue.push(nb[j]); }
      }
    }
    return last;
  }

  function isNodeVisible(idx) {
    var p = pts[idx];
    var margin = 50;
    if (p.x < margin || p.x > w - margin || p.y < margin || p.y > h - margin) return false;
    // Behind sidebar / theme toggle area (bottom-left)
    if (p.x < 220 && p.y > h - 120) return false;
    return true;
  }

  function startSearch() {
    snapshotAdj();
    searchType = cycleStep === 0 ? 'bfs' : 'dfs';

    // Find two distant visible nodes
    var best1 = -1, best2 = -1, bestDist = 0;
    for (var attempt = 0; attempt < 10; attempt++) {
      var a = Math.floor(Math.random() * pts.length);
      var far1 = bfsFarthest(a);
      var far2 = bfsFarthest(far1);
      if (!isNodeVisible(far1) || !isNodeVisible(far2)) continue;
      var dx = pts[far1].x - pts[far2].x;
      var dy = pts[far1].y - pts[far2].y;
      var d = Math.sqrt(dx * dx + dy * dy);
      if (d > bestDist) { bestDist = d; best1 = far1; best2 = far2; }
    }
    if (best1 < 0) {
      // Fallback: just pick any pair
      var a = Math.floor(Math.random() * pts.length);
      best1 = bfsFarthest(a);
      best2 = bfsFarthest(best1);
    }
    searchStart = best1;
    searchTarget = best2;
    searchVisited = new Set([searchStart]);
    searchParent = {};
    searchQueue = [searchStart];
    searchTraces = [];
    searchPathTraces = [];
    searchStepTimer = 0;
    searchStartFrame = frame;
  }

  /* ── Organize functions ── */
  function isInContentZone(x, y) {
    var contentLeft = 200 + (w - 200) * 0.2;
    var contentRight = 200 + (w - 200) * 0.8;
    var contentTop = h * 0.15;
    var contentBottom = h * 0.85;
    return x > contentLeft && x < contentRight && y > contentTop && y < contentBottom;
  }

  function startOrganize() {
    // Try multiple attempts to find a valid cluster
    for (var attempt = 0; attempt < 8; attempt++) {
      var seedIdx = Math.floor(Math.random() * pts.length);

      var visited = new Set([seedIdx]);
      var queue = [seedIdx];
      var cluster = [seedIdx];
      var targetCount = 14 + Math.floor(Math.random() * 10);
      targetCount = Math.min(targetCount, pts.length);

      while (queue.length && cluster.length < targetCount) {
        var cur = queue.shift();
        var nb = neighbors(cur, -1);
        for (var k = nb.length - 1; k > 0; k--) {
          var j = Math.floor(Math.random() * (k + 1));
          var tmp = nb[k]; nb[k] = nb[j]; nb[j] = tmp;
        }
        for (var i = 0; i < nb.length && cluster.length < targetCount; i++) {
          if (!visited.has(nb[i])) {
            visited.add(nb[i]);
            queue.push(nb[i]);
            cluster.push(nb[i]);
          }
        }
      }

      if (cluster.length < 8) continue;

      // Check centroid isn't in content zone
      var cx0 = 0, cy0 = 0;
      for (var i = 0; i < cluster.length; i++) {
        cx0 += pts[cluster[i]].x;
        cy0 += pts[cluster[i]].y;
      }
      cx0 /= cluster.length;
      cy0 /= cluster.length;
      if (isInContentZone(cx0, cy0)) continue;

      // Found a valid cluster — proceed
      var count = cluster.length;

      // Distribute into layers with random input/output sizes
      var input = 2 + Math.floor(Math.random() * Math.max(1, Math.floor(count * 0.15)));
      var output = 2 + Math.floor(Math.random() * Math.max(1, Math.floor(count * 0.08)));
      var remaining = count - input - output;
      if (remaining < 6) continue;
      var h1 = Math.max(3, Math.floor(remaining * 0.5));
      var h2 = Math.max(3, remaining - h1);
      if (output >= Math.min(h1, h2)) output = Math.min(h1, h2) - 1;
      if (output < 2) output = 2;
      var structure = [input, h1, h2, output];

      organizeLayers = [];
      var idx = 0;
      for (var l = 0; l < structure.length; l++) {
        var layer = [];
        for (var n = 0; n < structure[l] && idx < count; n++) {
          layer.push(cluster[idx++]);
        }
        organizeLayers.push(layer);
      }

      var cx = cx0, cy = cy0;

      var maxPerLayer = Math.max.apply(null, structure);
      var totalW = Math.min(maxPerLayer * 18, 140);
      var totalH = Math.min(maxPerLayer * 14, 120);
      var layerSpacing = totalW / (organizeLayers.length - 1);
      var startX = cx - totalW / 2;

      var slots = [];
      for (var l = 0; l < organizeLayers.length; l++) {
        var layer = organizeLayers[l];
        var lx = startX + l * layerSpacing;
        var layerH = totalH * (layer.length / maxPerLayer);
        var sy = cy - layerH / 2;
        var yGap = layer.length > 1 ? layerH / (layer.length - 1) : 0;
        for (var n = 0; n < layer.length; n++) {
          slots.push({ x: lx, y: layer.length > 1 ? sy + n * yGap : cy, layer: l, slotIdx: n });
        }
      }

      var assigned = new Set();
      var nodeForSlot = [];
      for (var s = 0; s < slots.length; s++) nodeForSlot.push(-1);
      var pairs = [];
      for (var s = 0; s < slots.length; s++) {
        for (var c = 0; c < cluster.length; c++) {
          var dx = pts[cluster[c]].x - slots[s].x;
          var dy = pts[cluster[c]].y - slots[s].y;
          pairs.push({ s: s, c: c, d: Math.sqrt(dx * dx + dy * dy) });
        }
      }
      pairs.sort(function (a, b) { return a.d - b.d; });
      var usedSlots = new Set();
      for (var p = 0; p < pairs.length; p++) {
        var si = pairs[p].s, ci = pairs[p].c;
        if (usedSlots.has(si) || assigned.has(ci)) continue;
        usedSlots.add(si);
        assigned.add(ci);
        nodeForSlot[si] = ci;
      }

      organizeLayers = [];
      var slotI = 0;
      for (var l = 0; l < structure.length; l++) {
        var layer = [];
        for (var n = 0; n < structure[l] && slotI < slots.length; n++) {
          if (nodeForSlot[slotI] >= 0) layer.push(cluster[nodeForSlot[slotI]]);
          slotI++;
        }
        layer.sort(function (a, b) { return pts[a].y - pts[b].y; });
        organizeLayers.push(layer);
      }

      organizeOrigins = {};
      organizeTargets = {};
      for (var l = 0; l < organizeLayers.length; l++) {
        var layerSlots = [];
        for (var s = 0; s < slots.length; s++) {
          if (slots[s].layer === l) layerSlots.push(slots[s]);
        }
        layerSlots.sort(function (a, b) { return a.y - b.y; });
        for (var n = 0; n < organizeLayers[l].length; n++) {
          var ni = organizeLayers[l][n];
          organizeOrigins[ni] = { x: pts[ni].x, y: pts[ni].y };
          organizeTargets[ni] = { x: layerSlots[n].x, y: layerSlots[n].y };
        }
      }

      organizePhase = 'forming';
      organizeTimer = 0;
      return;
    }
    // All attempts failed
    cycleStep = (cycleStep + 1) % 3;
    mode = 'normal';
    modeTimer = 600;
  }

  function smoothStep(t) {
    return t * t * (3 - 2 * t);
  }

  function updateOrganize() {
    organizeTimer++;
    var allNodes = [];
    for (var l = 0; l < organizeLayers.length; l++) {
      for (var n = 0; n < organizeLayers[l].length; n++) {
        allNodes.push(organizeLayers[l][n]);
      }
    }

    if (organizePhase === 'forming') {
      var t = smoothStep(Math.min(1, organizeTimer / ORGANIZE_FORM));
      for (var i = 0; i < allNodes.length; i++) {
        var ni = allNodes[i];
        pts[ni].x = organizeOrigins[ni].x + (organizeTargets[ni].x - organizeOrigins[ni].x) * t;
        pts[ni].y = organizeOrigins[ni].y + (organizeTargets[ni].y - organizeOrigins[ni].y) * t;
        pts[ni].vx = 0;
        pts[ni].vy = 0;
      }
      if (organizeTimer >= ORGANIZE_FORM) {
        organizePhase = 'hold';
        organizeTimer = 0;
      }
    } else if (organizePhase === 'hold') {
      for (var i = 0; i < allNodes.length; i++) {
        var ni = allNodes[i];
        pts[ni].x = organizeTargets[ni].x;
        pts[ni].y = organizeTargets[ni].y;
        pts[ni].vx = 0;
        pts[ni].vy = 0;
      }

      // Layer-by-layer: travel → glow → travel → glow ...
      if (nnHoldPhase === 'glowing') {
        nnGlowTimer++;
        // Fade glow out over time
        for (var key in nnNodeGlow) {
          nnNodeGlow[key] = nnNodeGlow[key] * 0.98;
        }
        if (nnGlowTimer >= NN_GLOW_DURATION) {
          nnNodeGlow = {};
          if (nnCurrentLayer < organizeLayers.length - 1) {
            // Fire signals to next layer
            var layerA = organizeLayers[nnCurrentLayer];
            var layerB = organizeLayers[nnCurrentLayer + 1];
            for (var a = 0; a < layerA.length; a++) {
              for (var b = 0; b < layerB.length; b++) {
                nnSignals.push({ from: layerA[a], to: layerB[b], t: 0 });
              }
            }
            nnCurrentLayer++;
            nnHoldPhase = 'traveling';
          }
        }
      } else if (nnHoldPhase === 'traveling') {
        var allDone = true;
        for (var i = nnSignals.length - 1; i >= 0; i--) {
          nnSignals[i].t += NN_SIGNAL_SPEED;
          if (nnSignals[i].t >= 1) {
            nnSignals.splice(i, 1);
          } else {
            allDone = false;
          }
        }
        if (allDone && nnSignals.length === 0) {
          // Signals arrived — light up current layer
          nnGlowTimer = 0;
          nnHoldPhase = 'glowing';
          var layer = organizeLayers[nnCurrentLayer];
          var isOutput = nnCurrentLayer === organizeLayers.length - 1;
          nnNodeGlow = {};
          if (isOutput) {
            // Only one node lights up
            var pick = Math.floor(Math.random() * layer.length);
            nnNodeGlow[layer[pick]] = 1;
            nnOutputNode = layer[pick];
          } else {
            for (var n = 0; n < layer.length; n++) {
              if (Math.random() < 0.3) continue; // ~30% stay dark
              nnNodeGlow[layer[n]] = 0.3 + Math.random() * 0.7;
            }
          }
        }
      } else {
        // Initial: light up input layer first
        nnHoldPhase = 'glowing';
        nnGlowTimer = 0;
        nnCurrentLayer = 0;
        var layer = organizeLayers[0];
        nnNodeGlow = {};
        for (var n = 0; n < layer.length; n++) {
          if (Math.random() < 0.3) continue;
          nnNodeGlow[layer[n]] = 0.3 + Math.random() * 0.7;
        }
      }

      // Exit hold: either forward pass complete, or safety timeout
      if ((nnHoldPhase === 'glowing' && nnCurrentLayer >= organizeLayers.length - 1 && nnGlowTimer >= NN_GLOW_DURATION) || organizeTimer > 900) {
        organizePhase = 'releasing';
        organizeTimer = 0;
        nnSignals = [];
        nnNodeGlow = {};
        nnHoldPhase = '';
        nnCurrentLayer = 0;
        if (nnOutputNode >= 0 && nnOutputNode < pts.length) {
          // Collect all nodes in the nn structure
          var nnSet = new Set();
          for (var l = 0; l < organizeLayers.length; l++) {
            for (var n = 0; n < organizeLayers[l].length; n++) {
              nnSet.add(organizeLayers[l][n]);
            }
          }
          // Find a neighbor outside the structure
          var nb = neighbors(nnOutputNode, -1);
          var outside = [];
          for (var n = 0; n < nb.length; n++) {
            if (!nnSet.has(nb[n])) outside.push(nb[n]);
          }
          if (outside.length) {
            var to = outside[Math.floor(Math.random() * outside.length)];
            var visited = new Set(nnSet);
            visited.add(nnOutputNode);
            signals.push({
              from: nnOutputNode, to: to, t: 0, hops: 0, alive: true,
              visited: visited,
              trail: [{ idx: nnOutputNode, frame: frame }]
            });
          }
        }
        nnOutputNode = -1;
        for (var i = 0; i < allNodes.length; i++) {
          var ni = allNodes[i];
          pts[ni].vx = (Math.random() - 0.5) * 0.25;
          pts[ni].vy = (Math.random() - 0.5) * 0.25;
        }
      }
    } else if (organizePhase === 'releasing') {
      // Let remaining nn signals fade
      for (var i = nnSignals.length - 1; i >= 0; i--) {
        nnSignals[i].t += NN_SIGNAL_SPEED;
        if (nnSignals[i].t >= 1) nnSignals.splice(i, 1);
      }
      if (organizeTimer >= ORGANIZE_RELEASE) {
        cycleStep = (cycleStep + 1) % 3;
        mode = 'normal';
        modeTimer = 1200 + Math.floor(Math.random() * 1200);
        organizeLayers = [];
        nnSignals = [];
        nnNodeGlow = {};
        nnHoldPhase = '';
        nnOutputNode = -1;
      }
    }
  }

  function searchStep() {
    if (!searchQueue.length) { mode = 'fadeout'; return; }

    var current;
    if (searchType === 'bfs') {
      current = searchQueue.shift();
    } else {
      current = searchQueue.pop();
    }

    if (current === searchTarget) {
      // Reconstruct path
      var cur = searchTarget;
      var path = [cur];
      while (cur !== searchStart && searchParent[cur] !== undefined) {
        cur = searchParent[cur];
        path.unshift(cur);
      }
      for (var k = 0; k < path.length - 1; k++) {
        searchPathTraces.push({ from: path[k], to: path[k + 1], frame: frame });
      }
      // Spawn idea from end node, avoiding shortest path nodes
      var pathSet = new Set(path);
      var endNb = neighbors(searchTarget, -1);
      var outside = [];
      for (var k = 0; k < endNb.length; k++) {
        if (!pathSet.has(endNb[k])) outside.push(endNb[k]);
      }
      if (outside.length) {
        var to = outside[Math.floor(Math.random() * outside.length)];
        var visited = new Set(pathSet);
        visited.add(searchTarget);
        signals.push({
          from: searchTarget, to: to, t: 0, hops: 0, alive: true,
          visited: visited,
          trail: [{ idx: searchTarget, frame: frame }]
        });
      }
      mode = 'fadeout';
      return;
    }

    var nb = adjSnapshot[current] || [];
    // Shuffle
    var shuffled = nb.slice();
    for (var k = shuffled.length - 1; k > 0; k--) {
      var j = Math.floor(Math.random() * (k + 1));
      var tmp = shuffled[k]; shuffled[k] = shuffled[j]; shuffled[j] = tmp;
    }

    for (var i = 0; i < shuffled.length; i++) {
      var n = shuffled[i];
      if (!searchVisited.has(n)) {
        searchVisited.add(n);
        searchParent[n] = current;
        searchQueue.push(n);
        searchTraces.push({ from: current, to: n, frame: frame });
      }
    }
  }

  /* ── Signal & mode update ── */
  function updateSignals() {
    // Mode logic
    if (mode === 'normal') {
      modeTimer--;
      if (modeTimer <= 0) {
        mode = 'waiting';
      }
      // Normal spawning
      spawnTimer++;
      if (spawnTimer >= SPAWN_INTERVAL && signals.length < MAX_SIGNALS) {
        spawnSignal();
        spawnTimer = 0;
      }
    } else if (mode === 'waiting') {
      if (signals.length === 0) {
        if (cycleStep <= 1) {
          startSearch();
          mode = 'search';
        } else {
          startOrganize();
          if (mode !== 'normal') mode = 'organize';
        }
      }
    } else if (mode === 'search') {
      searchStepTimer++;
      if (searchStepTimer >= SEARCH_STEP_RATE) {
        var stepsPerTick = 2;
        for (var si = 0; si < stepsPerTick && mode === 'search'; si++) {
          searchStep();
        }
        searchStepTimer = 0;
      }
    } else if (mode === 'organize') {
      updateOrganize();
    } else if (mode === 'fadeout') {
      var allFaded = true;
      for (var i = 0; i < searchTraces.length; i++) {
        if (frame - searchTraces[i].frame < SEARCH_TRACE_FADE) { allFaded = false; break; }
      }
      if (allFaded) {
        for (var i = 0; i < searchPathTraces.length; i++) {
          if (frame - searchPathTraces[i].frame < SEARCH_TRACE_FADE) { allFaded = false; break; }
        }
      }
      if (allFaded) {
        searchTraces = [];
        searchPathTraces = [];
        cycleStep = (cycleStep + 1) % 3;
        mode = 'normal';
        modeTimer = 1200 + Math.floor(Math.random() * 1200);
      }
    }

    // Update existing idea signals
    for (let i = signals.length - 1; i >= 0; i--) {
      const s = signals[i];

      if (s.alive) {
        const dx = pts[s.to].x - pts[s.from].x;
        const dy = pts[s.to].y - pts[s.from].y;
        const edgeLen = Math.sqrt(dx * dx + dy * dy) || 1;
        s.t += SIGNAL_PX_SPEED / edgeLen;

        if (s.t >= 1) {
          s.hops++;
          s.visited.add(s.to);
          s.trail.push({ idx: s.to, frame: frame });

          var allNb = neighbors(s.to, -1).filter(function (n) { return !s.visited.has(n); });
          if (!allNb.length || s.hops >= MAX_HOPS) {
            s.alive = false;
          } else {
            for (var k = allNb.length - 1; k > 0; k--) {
              var j = Math.floor(Math.random() * (k + 1));
              var tmp = allNb[k]; allNb[k] = allNb[j]; allNb[j] = tmp;
            }
            s.from = s.to;
            s.to = allNb[0];
            s.t = 0;
            var branches = Math.min(allNb.length, 3);
            for (var b = 1; b < branches && signals.length < MAX_SIGNALS; b++) {
              var childVisited = new Set(s.visited);
              signals.push({
                from: s.from, to: allNb[b], t: 0,
                hops: s.hops, alive: true,
                visited: childVisited,
                trail: s.trail.map(function (e) { return { idx: e.idx, frame: e.frame }; })
              });
            }
          }
        }
      }

      if (!s.alive) {
        var newest = s.trail[s.trail.length - 1].frame;
        if (frame - newest >= TRAIL_FADE) {
          signals.splice(i, 1);
        }
      }
    }
  }

  function alpha(px, py) {
    const dx = px - mouseX;
    const dy = py - mouseY;
    const d = Math.sqrt(dx * dx + dy * dy);
    if (d > GLOW_RADIUS) return BASE_ALPHA;
    const t = 1 - d / GLOW_RADIUS;
    return BASE_ALPHA + (BRIGHT_ALPHA - BASE_ALPHA) * t * t;
  }

  function isLight() {
    return document.documentElement.getAttribute('data-theme') === 'light';
  }

  function draw() {
    ctx.clearRect(0, 0, w, h);
    const light = isLight();
    const rgb = light ? '30,30,50' : '255,255,255';

    // Edges
    for (let i = 0; i < pts.length; i++) {
      for (let j = i + 1; j < pts.length; j++) {
        const dx = pts[i].x - pts[j].x;
        const dy = pts[i].y - pts[j].y;
        const d = Math.sqrt(dx * dx + dy * dy);
        if (d < LINK_DIST) {
          const mx = (pts[i].x + pts[j].x) / 2;
          const my = (pts[i].y + pts[j].y) / 2;
          const baseA = alpha(mx, my);
          if (light && baseA <= BASE_ALPHA) continue;
          const a = baseA * (1 - d / LINK_DIST);
          ctx.strokeStyle = 'rgba(' + rgb + ',' + a + ')';
          ctx.lineWidth = 0.5;
          ctx.beginPath();
          ctx.moveTo(pts[i].x, pts[i].y);
          ctx.lineTo(pts[j].x, pts[j].y);
          ctx.stroke();
        }
      }
    }

    // Nodes
    for (const p of pts) {
      const a = alpha(p.x, p.y) * 1.6;
      ctx.fillStyle = 'rgba(' + rgb + ',' + a + ')';
      ctx.beginPath();
      ctx.arc(p.x, p.y, 1.5, 0, Math.PI * 2);
      ctx.fill();
    }

    // NN node glow during organize
    if (mode === 'organize') {
      var gc = light ? '90,50,220' : '124,106,247';
      for (var idx in nnNodeGlow) {
        var intensity = nnNodeGlow[idx];
        if (intensity < 0.01) continue;
        var ni = parseInt(idx);
        if (ni >= pts.length) continue;
        var px = pts[ni].x, py = pts[ni].y;
        var grad = ctx.createRadialGradient(px, py, 0, px, py, 14);
        grad.addColorStop(0, 'rgba(' + gc + ',' + intensity * 0.5 + ')');
        grad.addColorStop(1, 'rgba(' + gc + ',0)');
        ctx.fillStyle = grad;
        ctx.beginPath();
        ctx.arc(px, py, 14, 0, Math.PI * 2);
        ctx.fill();
        ctx.fillStyle = 'rgba(' + gc + ',' + intensity * 0.7 + ')';
        ctx.beginPath();
        ctx.arc(px, py, 2.5, 0, Math.PI * 2);
        ctx.fill();
      }
    }

    // Idea signal traces
    var purple = light ? '90,50,220' : '124,106,247';

    for (const s of signals) {
      for (let k = 0; k < s.trail.length - 1; k++) {
        var age = frame - s.trail[k + 1].frame;
        var fade = Math.max(0, 1 - age / TRAIL_FADE) * 0.3;
        if (fade <= 0) continue;
        var a = pts[s.trail[k].idx];
        var b = pts[s.trail[k + 1].idx];
        ctx.strokeStyle = 'rgba(' + purple + ',' + fade + ')';
        ctx.lineWidth = 1;
        ctx.beginPath();
        ctx.moveTo(a.x, a.y);
        ctx.lineTo(b.x, b.y);
        ctx.stroke();
      }

      if (s.alive) {
        var p1 = pts[s.from];
        var p2 = pts[s.to];
        var x = p1.x + (p2.x - p1.x) * s.t;
        var y = p1.y + (p2.y - p1.y) * s.t;
        ctx.strokeStyle = 'rgba(' + purple + ',0.3)';
        ctx.lineWidth = 1;
        ctx.beginPath();
        ctx.moveTo(p1.x, p1.y);
        ctx.lineTo(x, y);
        ctx.stroke();
      }
    }

    // Search exploration traces
    var searchColor = light ? '60,80,200' : '100,140,235';
    for (var i = 0; i < searchTraces.length; i++) {
      var t = searchTraces[i];
      var age = frame - t.frame;
      var fade = Math.max(0, 1 - age / SEARCH_TRACE_FADE) * 0.2;
      if (fade <= 0) continue;
      var pa = pts[t.from];
      var pb = pts[t.to];
      ctx.strokeStyle = 'rgba(' + searchColor + ',' + fade + ')';
      ctx.lineWidth = 1;
      ctx.beginPath();
      ctx.moveTo(pa.x, pa.y);
      ctx.lineTo(pb.x, pb.y);
      ctx.stroke();
    }

    // Search found path
    var pathColor = light ? '70,50,180' : '124,106,247';
    for (var i = 0; i < searchPathTraces.length; i++) {
      var t = searchPathTraces[i];
      var age = frame - t.frame;
      var fade = Math.max(0, 1 - age / SEARCH_TRACE_FADE) * 0.3;
      if (fade <= 0) continue;
      var pa = pts[t.from];
      var pb = pts[t.to];
      ctx.strokeStyle = 'rgba(' + pathColor + ',' + fade + ')';
      ctx.lineWidth = 1.2;
      ctx.beginPath();
      ctx.moveTo(pa.x, pa.y);
      ctx.lineTo(pb.x, pb.y);
      ctx.stroke();
    }

    // Highlight start and target during search
    if (mode === 'search' || mode === 'fadeout') {
      var dotColor = light ? '90,50,220' : '150,130,255';
      var fadeIn = Math.min(1, (frame - searchStartFrame) / 60);
      var sf = mode === 'search' ? 0.6 * fadeIn : Math.max(0, 1 - (frame - (searchPathTraces[0]?.frame || frame)) / SEARCH_TRACE_FADE) * 0.6;
      if (sf > 0) {
        [searchStart, searchTarget].forEach(function (idx) {
          if (idx < 0 || idx >= pts.length) return;
          var px = pts[idx].x, py = pts[idx].y;
          // Outer glow
          var glow = ctx.createRadialGradient(px, py, 0, px, py, 18);
          glow.addColorStop(0, 'rgba(' + dotColor + ',' + sf * 0.5 + ')');
          glow.addColorStop(1, 'rgba(' + dotColor + ',0)');
          ctx.fillStyle = glow;
          ctx.beginPath();
          ctx.arc(px, py, 18, 0, Math.PI * 2);
          ctx.fill();
          // Core
          ctx.fillStyle = 'rgba(' + dotColor + ',' + sf + ')';
          ctx.beginPath();
          ctx.arc(px, py, 3.5, 0, Math.PI * 2);
          ctx.fill();
        });
      }
    }

    // Organize: draw nn signal traces flowing through layers
    if (nnSignals.length > 0) {
      var oc = light ? '90,50,220' : '124,106,247';
      for (var i = 0; i < nnSignals.length; i++) {
        var ns = nnSignals[i];
        var p1 = pts[ns.from];
        var p2 = pts[ns.to];
        var x = p1.x + (p2.x - p1.x) * ns.t;
        var y = p1.y + (p2.y - p1.y) * ns.t;

        // Trail behind the signal head
        var trail = 0.25;
        var t0 = Math.max(0, ns.t - trail);
        var tx = p1.x + (p2.x - p1.x) * t0;
        var ty = p1.y + (p2.y - p1.y) * t0;
        var trailGrad = ctx.createLinearGradient(tx, ty, x, y);
        trailGrad.addColorStop(0, 'rgba(' + oc + ',0)');
        trailGrad.addColorStop(1, 'rgba(' + oc + ',0.2)');
        ctx.strokeStyle = trailGrad;
        ctx.lineWidth = 1;
        ctx.beginPath();
        ctx.moveTo(tx, ty);
        ctx.lineTo(x, y);
        ctx.stroke();
      }
    }
  }

  function update() {
    // Gradually reveal nodes via BFS flood
    if (spawnQueue.length > 0) {
      var toAdd = Math.min(SPAWN_PER_FRAME, spawnQueue.length);
      for (var i = 0; i < toAdd; i++) {
        spawnNode(spawnQueue.shift());
      }
    } else if (spawned.size < allPts.length) {
      // Disconnected components — pick a random unspawned node
      for (var i = 0; i < allPts.length; i++) {
        if (!spawned.has(i)) { spawnNode(i); break; }
      }
    }

    var slowTarget = (mode === 'search') ? 0.3 : 1;
    if (typeof update.slow === 'undefined') update.slow = 1;
    update.slow += (slowTarget - update.slow) * 0.02;
    var slow = update.slow;
    for (const p of pts) {
      p.x += p.vx * slow;
      p.y += p.vy * slow;
      if (p.x < 0 || p.x > w) p.vx *= -1;
      if (p.y < 0 || p.y > h) p.vy *= -1;
    }
    updateSignals();
    frame++;
  }

  function loop() {
    update();
    draw();
    requestAnimationFrame(loop);
  }

  resize();
  seed();
  window.addEventListener('resize', () => { resize(); seed(); });
  window.addEventListener('mousemove', e => { mouseX = e.clientX; mouseY = e.clientY; });

  var NODE_GRAB_RADIUS = 20;
  var dragging = -1;
  var didDrag = false;

  function closestNode(x, y) {
    var best = -1, bestD = NODE_GRAB_RADIUS;
    for (var i = 0; i < pts.length; i++) {
      var dx = pts[i].x - x, dy = pts[i].y - y;
      var d = Math.sqrt(dx * dx + dy * dy);
      if (d < bestD) { bestD = d; best = i; }
    }
    return best;
  }

  document.addEventListener('mousedown', function (e) {
    dragging = closestNode(e.clientX, e.clientY);
    didDrag = false;
  });

  document.addEventListener('mousemove', function (e) {
    if (dragging >= 0) {
      pts[dragging].x = e.clientX;
      pts[dragging].y = e.clientY;
      pts[dragging].vx = 0;
      pts[dragging].vy = 0;
      didDrag = true;
    }
  });

  document.addEventListener('mouseup', function (e) {
    if (!didDrag) {
      if (dragging >= 0) {
        spawnSignalFrom(dragging);
      } else {
        pts.push({
          x: e.clientX,
          y: e.clientY,
          vx: (Math.random() - 0.5) * 0.25,
          vy: (Math.random() - 0.5) * 0.25,
        });
      }
    }
    dragging = -1;
  });

  loop();
})();
