// ============================================================
// Specs Browser — Dual-List Layout
// Left panel:  verified function contracts (accordion cards)
// Right panel: spec function definitions   (accordion cards)
// Sidebar:     module filter
// ============================================================

// ── Firebase Configuration ───────────────────────────────────
const FIREBASE_CONFIG = {
    apiKey: "",
    authDomain: "",
    projectId: "",
    storageBucket: "",
    messagingSenderId: "",
    appId: ""
};

const FIREBASE_ENABLED = FIREBASE_CONFIG.apiKey !== "";

// ── State ────────────────────────────────────────────────────
let verifiedFunctions = [];
let specFunctions = [];
let specLookup = {};              // specName -> spec object

let activeModule = null;          // module filter from sidebar
let searchLeft = "";              // search in left panel
let searchRight = "";             // search in right panel
let specFilterRefs = null;        // null = show all, or Set of spec names to filter right panel
let specFilterSource = "";        // display name of the function that set the filter

let db = null;
let commentsCache = {};

// ── Initialization ───────────────────────────────────────────
document.addEventListener("DOMContentLoaded", async () => {
    // Firebase
    if (FIREBASE_ENABLED && typeof firebase !== "undefined") {
        try {
            firebase.initializeApp(FIREBASE_CONFIG);
            db = firebase.firestore();
        } catch (e) {
            console.warn("Firebase init failed:", e);
        }
    }

    // Load data
    try {
        const response = await fetch("specs_data.json");
        const data = await response.json();
        verifiedFunctions = data.verified_functions || [];
        specFunctions = data.spec_functions || [];
    } catch (err) {
        document.getElementById("listLeft").innerHTML =
            '<div class="no-results"><h3>Failed to load data</h3><p>Could not load specs_data.json</p></div>';
        console.error("Failed to load specs:", err);
        return;
    }

    // Build lookup
    for (const s of specFunctions) {
        specLookup[s.name] = s;
    }

    // Stats
    const modules = [...new Set(verifiedFunctions.map(v => v.module))];
    document.getElementById("totalVerified").textContent = verifiedFunctions.length;
    document.getElementById("totalSpecs").textContent = specFunctions.length;
    document.getElementById("totalModules").textContent = modules.length;

    // Build sidebar
    buildModuleTree(modules);

    // Initial render of both panels
    renderLeftPanel();
    renderRightPanel();

    // Event listeners
    document.getElementById("searchLeft").addEventListener("input", e => {
        searchLeft = e.target.value.toLowerCase().trim();
        renderLeftPanel();
    });
    document.getElementById("searchRight").addEventListener("input", e => {
        searchRight = e.target.value.toLowerCase().trim();
        renderRightPanel();
    });
    document.getElementById("specFilterClear").addEventListener("click", clearSpecFilter);

    document.getElementById("expandAllLeft").addEventListener("click", () => toggleAllIn("listLeft", true));
    document.getElementById("collapseAllLeft").addEventListener("click", () => toggleAllIn("listLeft", false));
    document.getElementById("expandAllRight").addEventListener("click", () => toggleAllIn("listRight", true));
    document.getElementById("collapseAllRight").addEventListener("click", () => toggleAllIn("listRight", false));
});

// ── Module filter (horizontal pills) ─────────────────────────
function buildModuleTree(modules) {
    const container = document.getElementById("moduleTree");

    const allPill = createModulePill("All", verifiedFunctions.length, null);
    allPill.classList.add("active");
    container.appendChild(allPill);

    const sorted = [...modules].sort();
    for (const mod of sorted) {
        const count = verifiedFunctions.filter(v => v.module === mod).length;
        container.appendChild(createModulePill(mod, count, mod));
    }
}

function createModulePill(displayName, count, moduleId) {
    const el = document.createElement("span");
    el.className = "module-pill";
    el.innerHTML = `
        ${displayName}
        <span class="pill-count">${count}</span>
    `;
    el.addEventListener("click", () => {
        document.querySelectorAll(".module-pill").forEach(m => m.classList.remove("active"));
        el.classList.add("active");
        activeModule = moduleId;
        renderLeftPanel();
    });
    return el;
}

// ── Left panel: verified functions ───────────────────────────
function getFilteredVerified() {
    let list = verifiedFunctions;
    if (activeModule) {
        list = list.filter(v => v.module === activeModule);
    }
    if (searchLeft) {
        list = list.filter(v => {
            const h = (
                v.name + " " + v.display_name + " " + v.module + " " +
                v.contract + " " + (v.doc_comment || "") + " " +
                (v.math_interpretation || "") + " " + (v.informal_interpretation || "") +
                " " + (v.referenced_specs || []).join(" ")
            ).toLowerCase();
            return h.includes(searchLeft);
        });
    }
    list.sort((a, b) => a.module.localeCompare(b.module) || a.display_name.localeCompare(b.display_name));
    return list;
}

function renderLeftPanel() {
    const container = document.getElementById("listLeft");
    const countEl = document.getElementById("countLeft");
    const filtered = getFilteredVerified();

    if (filtered.length === 0) {
        container.innerHTML = '<div class="no-results"><h3>No matching functions</h3><p>Try a different search or module.</p></div>';
        countEl.textContent = "0";
        return;
    }

    countEl.textContent = filtered.length;

    let html = "";
    let currentMod = null;
    for (const fn of filtered) {
        if (fn.module !== currentMod) {
            currentMod = fn.module;
            html += `<div class="module-group-header">${escapeHtml(currentMod)}</div>`;
        }
        html += renderVerifiedCard(fn);
    }

    container.innerHTML = html;

    // Syntax highlight
    container.querySelectorAll("pre code.language-rust").forEach(b => Prism.highlightElement(b));

    // Card toggle
    container.querySelectorAll(".spec-header").forEach(h => {
        h.addEventListener("click", () => h.closest(".spec-card").classList.toggle("open"));
    });

    // Copy buttons
    container.querySelectorAll(".copy-btn").forEach(btn => {
        btn.addEventListener("click", e => {
            e.stopPropagation();
            const code = btn.closest(".spec-code-wrapper").querySelector("code").textContent;
            navigator.clipboard.writeText(code).then(() => {
                btn.textContent = "Copied!";
                setTimeout(() => { btn.textContent = "Copy"; }, 1500);
            });
        });
    });

    // "Show referenced specs" buttons
    container.querySelectorAll(".show-refs-btn").forEach(btn => {
        btn.addEventListener("click", e => {
            e.stopPropagation();
            const fnId = btn.dataset.fnId;
            const fn = verifiedFunctions.find(v => v.id === fnId);
            if (fn && fn.referenced_specs && fn.referenced_specs.length > 0) {
                setSpecFilter(fn.referenced_specs, fn.display_name);
            }
        });
    });

    // Spec-link clicks (in contract code) — scroll to / highlight the spec card on the right
    container.querySelectorAll(".spec-link").forEach(link => {
        link.addEventListener("click", e => {
            e.stopPropagation();
            scrollToSpecCard(link.dataset.spec);
        });
    });

    // Ref-tag clicks
    container.querySelectorAll(".contract-ref-tag").forEach(tag => {
        tag.addEventListener("click", e => {
            e.stopPropagation();
            scrollToSpecCard(tag.dataset.spec);
        });
    });

    // Comment toggle
    container.querySelectorAll(".comments-toggle").forEach(btn => {
        btn.addEventListener("click", () => {
            const content = btn.nextElementSibling;
            content.classList.toggle("open");
            if (content.classList.contains("open")) {
                loadComments(btn.dataset.fnId, content);
            }
        });
    });
}

function renderVerifiedCard(fn) {
    const hasDoc = fn.doc_comment && fn.doc_comment.trim();
    const hasMath = fn.math_interpretation && fn.math_interpretation.trim();
    const hasInformal = fn.informal_interpretation && fn.informal_interpretation.trim();
    const hasInterpretations = hasMath || hasInformal;
    const hasRefs = fn.referenced_specs && fn.referenced_specs.length > 0;

    const docHtml = hasDoc
        ? fn.doc_comment.split("\n").filter(Boolean).map(p => `<p>${escapeHtml(p)}</p>`).join("")
        : "";

    const contractHtml = highlightSpecNames(fn.contract, fn.referenced_specs || []);

    const refsHtml = hasRefs ? `
        <div class="contract-refs">
            <div class="contract-refs-label">Referenced Spec Functions</div>
            <div class="contract-refs-list">
                ${fn.referenced_specs.map(s => `<span class="contract-ref-tag" data-spec="${escapeHtml(s)}" title="Click to scroll to definition">${escapeHtml(s)}</span>`).join("")}
            </div>
        </div>` : "";

    const showRefsBtn = hasRefs ? `
        <button class="show-refs-btn" data-fn-id="${fn.id}" title="Filter right panel to show only referenced specs">
            Focus referenced specs <span class="refs-count">${fn.referenced_specs.length}</span>
        </button>` : "";

    return `
    <div class="spec-card" data-id="${fn.id}" data-module="${fn.module}">
        <div class="spec-header">
            <div class="spec-toggle">&#9654;</div>
            <div class="spec-info">
                <div class="spec-name">${escapeHtml(fn.display_name)}</div>
                <div class="spec-meta">
                    <span class="spec-module">${escapeHtml(fn.module)}</span>
                    ${hasMath ? `<span class="spec-math">${escapeHtml(fn.math_interpretation)}</span>` : ""}
                </div>
            </div>
            <a class="spec-github" href="${fn.github_link}" target="_blank" rel="noopener"
               title="View source on GitHub" onclick="event.stopPropagation()">
                Source &nearr;
            </a>
        </div>
        <div class="spec-body">
            ${hasDoc ? `<div class="spec-doc">${docHtml}</div>` : ""}
            ${hasInterpretations ? `
            <div class="spec-interpretations">
                ${hasMath ? `<div class="spec-interp"><span class="spec-interp-label">Math:</span> <span class="spec-interp-value">${escapeHtml(fn.math_interpretation)}</span></div>` : ""}
                ${hasInformal ? `<div class="spec-interp"><span class="spec-interp-label">Meaning:</span> <span class="spec-interp-value">${escapeHtml(fn.informal_interpretation)}</span></div>` : ""}
            </div>` : ""}
            ${refsHtml}
            ${showRefsBtn}
            <div class="spec-code-wrapper">
                <button class="copy-btn">Copy</button>
                <pre><code class="language-rust">${contractHtml}</code></pre>
            </div>
            <div class="spec-comments">
                <button class="comments-toggle" data-fn-id="${fn.id}">
                    <span>Comments</span>
                    <span class="comment-count" id="count-${fn.id}">...</span>
                </button>
                <div class="comments-content" id="comments-${fn.id}"></div>
            </div>
        </div>
    </div>`;
}

// ── Right panel: spec functions ──────────────────────────────
function getFilteredSpecs() {
    let list = specFunctions;

    // Filter by referenced specs (from "Show referenced specs" button)
    if (specFilterRefs) {
        list = list.filter(s => specFilterRefs.has(s.name));
    }

    if (searchRight) {
        list = list.filter(s => {
            const h = (
                s.name + " " + s.module + " " + s.signature + " " + s.body + " " +
                (s.doc_comment || "") + " " + (s.math_interpretation || "") +
                " " + (s.informal_interpretation || "")
            ).toLowerCase();
            return h.includes(searchRight);
        });
    }

    list.sort((a, b) => a.module.localeCompare(b.module) || a.name.localeCompare(b.name));
    return list;
}

function renderRightPanel() {
    const container = document.getElementById("listRight");
    const countEl = document.getElementById("countRight");
    const banner = document.getElementById("specFilterBanner");
    const bannerText = document.getElementById("specFilterText");

    // Show/hide filter banner
    if (specFilterRefs) {
        banner.style.display = "flex";
        bannerText.textContent = `Showing ${specFilterRefs.size} specs related to ${specFilterSource}`;
    } else {
        banner.style.display = "none";
    }

    const filtered = getFilteredSpecs();

    if (filtered.length === 0) {
        container.innerHTML = '<div class="no-results"><h3>No matching specs</h3><p>Try a different search or clear the filter.</p></div>';
        countEl.textContent = "0";
        return;
    }

    countEl.textContent = filtered.length;

    let html = "";
    let currentMod = null;
    for (const spec of filtered) {
        if (spec.module !== currentMod) {
            currentMod = spec.module;
            html += `<div class="module-group-header">${escapeHtml(currentMod)}</div>`;
        }
        html += renderSpecCard(spec);
    }

    container.innerHTML = html;

    // Syntax highlight
    container.querySelectorAll("pre code.language-rust").forEach(b => Prism.highlightElement(b));

    // Card toggle
    container.querySelectorAll(".spec-header").forEach(h => {
        h.addEventListener("click", () => h.closest(".spec-card").classList.toggle("open"));
    });

    // Copy buttons
    container.querySelectorAll(".copy-btn").forEach(btn => {
        btn.addEventListener("click", e => {
            e.stopPropagation();
            const code = btn.closest(".spec-code-wrapper").querySelector("code").textContent;
            navigator.clipboard.writeText(code).then(() => {
                btn.textContent = "Copied!";
                setTimeout(() => { btn.textContent = "Copy"; }, 1500);
            });
        });
    });

    // "Show referenced specs" buttons on spec cards — inline toggle
    container.querySelectorAll(".spec-show-deps-btn").forEach(btn => {
        btn.addEventListener("click", e => {
            e.stopPropagation();
            const specName = btn.dataset.specName;
            const inlineContainer = btn.nextElementSibling; // .inline-refs-container
            if (!inlineContainer) return;

            const isOpen = inlineContainer.style.display !== "none";
            if (isOpen) {
                inlineContainer.style.display = "none";
                btn.classList.remove("active");
                return;
            }

            // Build inline cards for each referenced spec
            const spec = specLookup[specName];
            if (!spec || !spec.referenced_specs) return;

            const html = spec.referenced_specs.map(refName => {
                const refSpec = specLookup[refName];
                if (!refSpec) return `<div class="inline-ref-card"><div class="inline-ref-name">${escapeHtml(refName)}</div><div class="inline-ref-missing">Definition not found</div></div>`;
                return renderInlineRefCard(refSpec);
            }).join("");

            inlineContainer.innerHTML = html;
            inlineContainer.style.display = "block";
            btn.classList.add("active");

            // Syntax highlight the new code blocks
            inlineContainer.querySelectorAll("pre code").forEach(block => Prism.highlightElement(block));

            // Toggle inline cards open/closed
            inlineContainer.querySelectorAll(".inline-ref-header").forEach(h => {
                h.addEventListener("click", () => h.closest(".inline-ref-card").classList.toggle("open"));
            });

            // Scroll-to-spec clicks on tags inside inline cards
            inlineContainer.querySelectorAll(".spec-to-spec-tag").forEach(tag => {
                tag.addEventListener("click", ev => {
                    ev.stopPropagation();
                    scrollToSpecCard(tag.dataset.spec);
                });
            });
        });
    });

    // Spec-to-spec ref tag clicks — scroll to that spec card
    container.querySelectorAll(".spec-to-spec-tag").forEach(tag => {
        tag.addEventListener("click", e => {
            e.stopPropagation();
            scrollToSpecCard(tag.dataset.spec);
        });
    });

    // Comment toggle
    container.querySelectorAll(".comments-toggle").forEach(btn => {
        btn.addEventListener("click", () => {
            const content = btn.nextElementSibling;
            content.classList.toggle("open");
            if (content.classList.contains("open")) {
                loadComments(btn.dataset.fnId, content);
            }
        });
    });
}

function renderInlineRefCard(spec) {
    const escapedBody = escapeHtml(spec.body);
    const hasMath = spec.math_interpretation && spec.math_interpretation.trim();
    const hasNestedRefs = spec.referenced_specs && spec.referenced_specs.length > 0;
    const nestedTagsHtml = hasNestedRefs
        ? `<div class="inline-ref-tags">${spec.referenced_specs.map(s => `<span class="contract-ref-tag spec-to-spec-tag" data-spec="${escapeHtml(s)}" title="Scroll to definition">${escapeHtml(s)}</span>`).join("")}</div>`
        : "";
    return `
    <div class="inline-ref-card">
        <div class="inline-ref-header">
            <span class="inline-ref-toggle">&#9654;</span>
            <span class="inline-ref-name">${escapeHtml(spec.name)}</span>
            <span class="inline-ref-module">${escapeHtml(spec.module)}</span>
            ${hasMath ? `<span class="inline-ref-math">${escapeHtml(spec.math_interpretation)}</span>` : ""}
        </div>
        <div class="inline-ref-body">
            ${nestedTagsHtml}
            <pre><code class="language-rust">${escapedBody}</code></pre>
        </div>
    </div>`;
}

function renderSpecCard(spec) {
    const escapedBody = escapeHtml(spec.body);
    const hasDoc = spec.doc_comment && spec.doc_comment.trim();
    const hasMath = spec.math_interpretation && spec.math_interpretation.trim();
    const hasInformal = spec.informal_interpretation && spec.informal_interpretation.trim();
    const hasInterpretations = hasMath || hasInformal;
    const hasRefs = spec.referenced_specs && spec.referenced_specs.length > 0;

    const docHtml = hasDoc
        ? spec.doc_comment.split("\n").filter(Boolean).map(p => `<p>${escapeHtml(p)}</p>`).join("")
        : "";

    const refsHtml = hasRefs ? `
        <div class="contract-refs">
            <div class="contract-refs-label">Uses Spec Functions</div>
            <div class="contract-refs-list">
                ${spec.referenced_specs.map(s => `<span class="contract-ref-tag spec-to-spec-tag" data-spec="${escapeHtml(s)}" title="Click to scroll to definition">${escapeHtml(s)}</span>`).join("")}
            </div>
        </div>` : "";

    const showRefsBtn = hasRefs ? `
        <button class="show-refs-btn spec-show-deps-btn" data-spec-name="${escapeHtml(spec.name)}" title="Expand referenced spec definitions below">
            Show referenced specs <span class="refs-count">${spec.referenced_specs.length}</span>
        </button>
        <div class="inline-refs-container" data-for-spec="${escapeHtml(spec.name)}" style="display:none;"></div>` : "";

    return `
    <div class="spec-card" data-id="${spec.id}" data-spec-name="${spec.name}" data-module="${spec.module}">
        <div class="spec-header">
            <div class="spec-toggle">&#9654;</div>
            <div class="spec-info">
                <div class="spec-name">${escapeHtml(spec.name)}</div>
                <div class="spec-meta">
                    <span class="spec-module">${escapeHtml(spec.module)}</span>
                    ${spec.visibility ? `<span class="spec-visibility">${escapeHtml(spec.visibility)}</span>` : ""}
                    ${hasMath ? `<span class="spec-math">${escapeHtml(spec.math_interpretation)}</span>` : ""}
                </div>
            </div>
            <a class="spec-github" href="${spec.github_link}" target="_blank" rel="noopener"
               title="View source on GitHub" onclick="event.stopPropagation()">
                Source &nearr;
            </a>
        </div>
        <div class="spec-body">
            ${hasDoc ? `<div class="spec-doc">${docHtml}</div>` : ""}
            ${hasInterpretations ? `
            <div class="spec-interpretations">
                ${hasMath ? `<div class="spec-interp"><span class="spec-interp-label">Math:</span> <span class="spec-interp-value">${escapeHtml(spec.math_interpretation)}</span></div>` : ""}
                ${hasInformal ? `<div class="spec-interp"><span class="spec-interp-label">Meaning:</span> <span class="spec-interp-value">${escapeHtml(spec.informal_interpretation)}</span></div>` : ""}
            </div>` : ""}
            ${refsHtml}
            ${showRefsBtn}
            <div class="spec-code-wrapper">
                <button class="copy-btn">Copy</button>
                <pre><code class="language-rust">${escapedBody}</code></pre>
            </div>
            <div class="spec-comments">
                <button class="comments-toggle" data-fn-id="${spec.id}">
                    <span>Comments</span>
                    <span class="comment-count" id="count-${spec.id}">...</span>
                </button>
                <div class="comments-content" id="comments-${spec.id}"></div>
            </div>
        </div>
    </div>`;
}

// ── Spec filter (from "Show referenced specs" button) ────────
function setSpecFilter(refNames, sourceName) {
    specFilterRefs = new Set(refNames);
    specFilterSource = sourceName;
    renderRightPanel();
    // Scroll the right panel's own scroll container to top (not the page)
    const rightScroll = document.querySelector(".panel-right .panel-scroll");
    if (rightScroll) rightScroll.scrollTop = 0;
}

function clearSpecFilter() {
    specFilterRefs = null;
    specFilterSource = "";
    renderRightPanel();
}

// ── Scroll to and highlight a spec card on the right ─────────
function scrollToSpecCard(specName) {
    // If the right panel is filtered and the target isn't visible, clear filter first
    if (specFilterRefs && !specFilterRefs.has(specName)) {
        clearSpecFilter();
    }

    // Find the card
    const card = document.querySelector(`.panel-right .spec-card[data-spec-name="${specName}"]`);
    if (!card) return;

    // Open it
    card.classList.add("open");

    // Highlight briefly
    card.classList.add("highlight-card");
    setTimeout(() => card.classList.remove("highlight-card"), 2500);

    // Scroll within the right panel's own scroll container (not the page)
    const rightScroll = document.querySelector(".panel-right .panel-scroll");
    if (rightScroll) {
        const cardTop = card.offsetTop - rightScroll.offsetTop;
        rightScroll.scrollTo({ top: cardTop - 20, behavior: "smooth" });
    }
}

// ── Highlight spec names in contract text ────────────────────
function highlightSpecNames(contractText, referencedSpecs) {
    if (!referencedSpecs || referencedSpecs.length === 0) {
        return escapeHtml(contractText);
    }

    const sortedSpecs = [...referencedSpecs].sort((a, b) => b.length - a.length);
    const pattern = new RegExp(
        `\\b(${sortedSpecs.map(s => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')).join("|")})\\b`,
        "g"
    );

    const segments = [];
    let lastIndex = 0;
    let match;

    while ((match = pattern.exec(contractText)) !== null) {
        if (match.index > lastIndex) {
            segments.push({ type: "text", value: contractText.slice(lastIndex, match.index) });
        }
        segments.push({ type: "spec", value: match[1] });
        lastIndex = pattern.lastIndex;
    }
    if (lastIndex < contractText.length) {
        segments.push({ type: "text", value: contractText.slice(lastIndex) });
    }

    return segments.map(seg => {
        if (seg.type === "spec") {
            return `<span class="spec-link" data-spec="${escapeHtml(seg.value)}" title="Click to view definition">${escapeHtml(seg.value)}</span>`;
        }
        return escapeHtml(seg.value);
    }).join("");
}

// ── Expand / Collapse All ────────────────────────────────────
function toggleAllIn(containerId, open) {
    document.getElementById(containerId).querySelectorAll(".spec-card").forEach(card => {
        if (open) card.classList.add("open");
        else card.classList.remove("open");
    });
}

// ── Comments (Firebase) ──────────────────────────────────────
async function loadComments(functionId, container) {
    if (!FIREBASE_ENABLED || !db) {
        container.innerHTML = `
            <div class="firebase-notice">
                Commenting is not yet configured.<br>
                See <code>specs.js</code> FIREBASE_CONFIG to enable.
            </div>`;
        return;
    }

    container.innerHTML = `
        <div class="comment-list" id="list-${functionId}">
            <div class="comment-empty">Loading comments...</div>
        </div>
        <div class="comment-form">
            <input type="text" placeholder="Your name" maxlength="100" id="name-${functionId}">
            <textarea placeholder="Your comment..." maxlength="2000" id="msg-${functionId}"></textarea>
            <button onclick="submitComment('${functionId}')">Post Comment</button>
        </div>`;

    try {
        const snapshot = await db.collection("comments")
            .where("functionId", "==", functionId)
            .orderBy("timestamp", "asc")
            .get();
        const comments = [];
        snapshot.forEach(doc => comments.push(doc.data()));
        commentsCache[functionId] = comments;
        renderComments(functionId, comments);
        const countEl = document.getElementById(`count-${functionId}`);
        if (countEl) countEl.textContent = comments.length;
    } catch (err) {
        console.error("Error loading comments:", err);
        const listEl = document.getElementById(`list-${functionId}`);
        if (listEl) listEl.innerHTML = `<div class="comment-empty">Could not load comments.</div>`;
    }
}

function renderComments(functionId, comments) {
    const listEl = document.getElementById(`list-${functionId}`);
    if (!listEl) return;
    if (comments.length === 0) {
        listEl.innerHTML = `<div class="comment-empty">No comments yet. Be the first!</div>`;
        return;
    }
    listEl.innerHTML = comments.map(c => {
        const time = c.timestamp?.toDate
            ? c.timestamp.toDate().toLocaleDateString("en-US", {
                month: "short", day: "numeric", year: "numeric",
                hour: "2-digit", minute: "2-digit"
              })
            : "";
        return `
            <div class="comment-item">
                <span class="comment-author">${escapeHtml(c.name)}</span>
                <span class="comment-time">${time}</span>
                <div class="comment-text">${escapeHtml(c.message)}</div>
            </div>`;
    }).join("");
}

window.submitComment = async function(functionId) {
    if (!db) return;
    const nameInput = document.getElementById(`name-${functionId}`);
    const msgInput = document.getElementById(`msg-${functionId}`);
    const name = nameInput.value.trim();
    const message = msgInput.value.trim();
    if (!name || !message) {
        alert("Please enter both your name and a comment.");
        return;
    }
    const btn = msgInput.closest(".comment-form").querySelector("button");
    btn.disabled = true;
    btn.textContent = "Posting...";
    try {
        await db.collection("comments").add({
            functionId, name, message,
            timestamp: firebase.firestore.FieldValue.serverTimestamp()
        });
        nameInput.value = "";
        msgInput.value = "";
        const container = document.getElementById(`comments-${functionId}`);
        if (container) await loadComments(functionId, container);
    } catch (err) {
        console.error("Error posting comment:", err);
        alert("Failed to post comment. Please try again.");
    } finally {
        btn.disabled = false;
        btn.textContent = "Post Comment";
    }
};

// ── Utilities ────────────────────────────────────────────────
function escapeHtml(str) {
    if (!str) return "";
    const div = document.createElement("div");
    div.textContent = str;
    return div.innerHTML;
}
