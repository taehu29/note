/**
 * note2.js - 2D Canvas & Note Application Controller
 * 
 * [설계 아키텍처]
 * Phase 1: Viewport & Grid (Pan, Zoom, Coordinate System)
 * Phase 2: In-Memory Data Store & Element Rendering (Box & Line)
 * Phase 3: Selection Manager & Transforms (Multi Drag, Edge Resize, Marquee)
 * Phase 4: History Management & Deletion
 * Phase 5: Add Mode & Creation Tools (Box & Line Creation)
 * Phase 6: Rich Text & LaTeX Renderer Integration
 * Phase 7: Local File Sync (File System Access API & IndexedDB)
 */

(function () {
    'use strict';

    // =========================================================================
    // 1. 상수 및 전역 설정 (Constants & Configurations)
    // =========================================================================
    const CONFIG = {
        DEFAULT_GRID_SIZE_EM: 200,      // 초기 그리드 너비/높이 (em)
        DEFAULT_CELL_SIZE_PX: 32,       // 1em 당 픽셀 (2em = 32px 기준)
        MIN_SCALE: 0.25,                // 최소 배율 (50%, 기준 scale 0.5 = 100%)
        MAX_SCALE: 1.0,                 // 최대 배율 (200%)
        DEFAULT_SCALE: 0.5 / Math.pow(1.1, 3), // 기본 배율 (~0.3756, 75%)
        ZOOM_FACTOR: 1.1,               // 줌 배율 단계 승수
        TOOLTIP_HIDE_DELAY_MS: 1000,    // 툴팁 자동 숨김 시간
        DEFAULT_BOX_WIDTH_EM: 18,       // 신규 박스 기본 너비 (em)
        DEFAULT_BOX_HEIGHT_EM: 10       // 신규 박스 기본 높이 (em)
    };

    // 규격화된 배율 단계 (scale 0.5 = 100% 기준, 1.1배 비율 고정)
    const ZOOM_STEPS = [
        0.25,                   // 50%
        0.5 / Math.pow(1.1, 6), // ~56%
        0.5 / Math.pow(1.1, 5), // ~62%
        0.5 / Math.pow(1.1, 4), // ~68%
        0.5 / Math.pow(1.1, 3), // ~75%
        0.5 / Math.pow(1.1, 2), // ~83%
        0.5 / 1.1,              // ~91%
        0.5,                    // 100% (기준)
        0.5 * 1.1,              // 110%
        0.5 * Math.pow(1.1, 2), // 121%
        0.5 * Math.pow(1.1, 3), // 133%
        0.5 * Math.pow(1.1, 4), // 146%
        0.5 * Math.pow(1.1, 5), // 161%
        0.5 * Math.pow(1.1, 6), // 177%
        1.0                     // 200%
    ];

    function getNextZoomStep(currentScale, isZoomIn) {
        const EPSILON = 0.0001;
        if (isZoomIn) {
            const next = ZOOM_STEPS.find(s => s > currentScale + EPSILON);
            return next !== undefined ? next : ZOOM_STEPS[ZOOM_STEPS.length - 1];
        } else {
            for (let i = ZOOM_STEPS.length - 1; i >= 0; i--) {
                if (ZOOM_STEPS[i] < currentScale - EPSILON) {
                    return ZOOM_STEPS[i];
                }
            }
            return ZOOM_STEPS[0];
        }
    }

    function getClosestZoomStep(targetScale) {
        let closest = ZOOM_STEPS[0];
        let minDiff = Math.abs(targetScale - closest);
        for (let i = 1; i < ZOOM_STEPS.length; i++) {
            const diff = Math.abs(targetScale - ZOOM_STEPS[i]);
            if (diff < minDiff) {
                minDiff = diff;
                closest = ZOOM_STEPS[i];
            }
        }
        return closest;
    }

    // =========================================================================
    // 2. KaTeX 수식 변환 및 텍스트 직렬화 유틸리티 (LaTeX & KaTeX Utils)
    // =========================================================================
    function escapeHtmlAttr(str) {
        return (str || '')
            .replace(/&/g, '&amp;')
            .replace(/"/g, '&quot;')
            .replace(/'/g, '&#39;')
            .replace(/</g, '&lt;')
            .replace(/>/g, '&gt;');
    }

    function prepareLatexForRender(latex, isDisplay = false) {
        if (!latex) return '';
        if (isDisplay) return latex;
        const trimmed = latex.trim();
        if (trimmed.startsWith('\\newcommand') || trimmed.startsWith('\\def') || trimmed.startsWith('\\displaystyle')) {
            return latex;
        }
        return '\\displaystyle ' + latex;
    }

    const mathRenderCache = new Map();
    const MAX_MATH_CACHE = 1500;

    function renderLatexToHtml(latex, isDisplay = false) {
        if (!latex) return '';
        const cacheKey = (isDisplay ? 'D:' : 'I:') + latex;
        if (mathRenderCache.has(cacheKey)) {
            return mathRenderCache.get(cacheKey);
        }

        let result = '';
        if (typeof katex !== 'undefined') {
            try {
                const expr = prepareLatexForRender(latex, isDisplay);
                result = katex.renderToString(expr, {
                    displayMode: isDisplay,
                    throwOnError: false,
                    trust: true
                });
            } catch (e) {
                console.error('KaTeX render error:', e);
                result = escapeHtmlAttr(latex);
            }
        } else {
            result = escapeHtmlAttr(latex);
        }

        if (mathRenderCache.size >= MAX_MATH_CACHE) {
            const firstKey = mathRenderCache.keys().next().value;
            mathRenderCache.delete(firstKey);
        }
        mathRenderCache.set(cacheKey, result);
        return result;
    }

    // =========================================================================
    // 2-B. TikZ 그래프 변환 유틸리티 (좌표 1 = 1em 고정 배율)
    // =========================================================================
    function convertTikzToSvg(tikzCode) {
        if (!tikzCode || !tikzCode.trim()) return '';

        let raw = tikzCode.trim();
        // 주석(%) 제거
        raw = raw.replace(/(?<!\\)%.*$/gm, '');

        if (!raw.includes('\\begin{tikzpicture}')) {
            raw = `\\begin{tikzpicture}\n${raw}\n\\end{tikzpicture}`;
        }

        raw = raw
            .replace(/<[^>]*>/g, ' ')
            .replace(/&gt;/g, '>')
            .replace(/&lt;/g, '<')
            .replace(/&amp;/g, '&')
            .replace(/&nbsp;|\u00a0/g, ' ');

        const svgId = 'tikz-' + Math.floor(Math.random() * 1000000);

        const envMatch = raw.match(/\\begin\{tikzpicture\}\s*(\[[^\]]*\])?/);
        const envOptions = envMatch && envMatch[1] ? envMatch[1] : '';

        // 기준: 좌표 1 = 1em (EM = 32px 내부 렌더링 해상도)
        const EM = 32;

        function parseUnit(valStr, defaultVal = 1 * EM) {
            if (!valStr) return defaultVal;
            valStr = valStr.trim().toLowerCase();
            if (valStr.endsWith('em')) return (parseFloat(valStr) || 1) * EM;
            if (valStr.endsWith('ex')) return (parseFloat(valStr) || 1) * 0.5 * EM;
            if (valStr.endsWith('px')) return parseFloat(valStr) || defaultVal;
            if (valStr.endsWith('cm')) return (parseFloat(valStr) || 1) * 37.8;
            if (valStr.endsWith('mm')) return (parseFloat(valStr) || 1) * 3.78;
            if (valStr.endsWith('pt')) return (parseFloat(valStr) || 1) * 1.33;
            if (valStr.endsWith('in')) return (parseFloat(valStr) || 1) * 96;
            const num = parseFloat(valStr);
            return isNaN(num) ? defaultVal : num * EM;
        }

        const scaleMatch = envOptions.match(/scale\s*=\s*([\d.]+)/);
        const globalScale = scaleMatch ? parseFloat(scaleMatch[1]) : 1;

        const xMatch = envOptions.match(/\bx\s*=\s*([^,\]]+)/);
        const yMatch = envOptions.match(/\by\s*=\s*([^,\]]+)/);

        // 기본 좌표 단위: 1em 고정 (EM = 32px)
        const scaleX = parseUnit(xMatch ? xMatch[1] : null, 1 * EM) * globalScale;
        const scaleY = parseUnit(yMatch ? yMatch[1] : null, 1 * EM) * globalScale;

        const contentMatch = raw.match(/\\begin\{tikzpicture\}\s*(?:\[[^\]]*\])?([\s\S]*?)\\end\{tikzpicture\}/);
        if (!contentMatch) return '';
        const body = contentMatch[1];

        let svgElements = [];
        let usedColors = new Set(['black', 'currentColor']);
        let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;

        function updateBounds(x, y) {
            if (isNaN(x) || isNaN(y)) return;
            if (x < minX) minX = x;
            if (x > maxX) maxX = x;
            if (y < minY) minY = y;
            if (y > maxY) maxY = y;
        }

        const namedCoords = new Map();

        function parseCoord(coordStr, refPt = null, doUpdateBounds = true) {
            if (!coordStr) return null;
            coordStr = coordStr.trim();

            // 명명된 좌표: (A)
            const nameMatch = coordStr.match(/^\(([a-zA-Z0-9_\-]+)\)$/);
            if (nameMatch && namedCoords.has(nameMatch[1])) {
                const pt = namedCoords.get(nameMatch[1]);
                if (doUpdateBounds) updateBounds(pt.x, pt.y);
                return { x: pt.x, y: pt.y };
            }

            // 극좌표: (deg : r)
            const polarMatch = coordStr.match(/\(\s*(-?[\d.]+)\s*:\s*(-?[\d.]+[a-zA-Z%]*)\s*\)/);
            if (polarMatch) {
                const angleDeg = parseFloat(polarMatch[1]);
                const angleRad = (angleDeg * Math.PI) / 180;
                const rVal = polarMatch[2];
                const r = /[a-zA-Z%]/.test(rVal.replace(/^-?[\d.]+/, '')) ? parseUnit(rVal, scaleX) : parseFloat(rVal) * scaleX;
                let x = r * Math.cos(angleRad);
                let y = -r * Math.sin(angleRad);
                if (refPt) {
                    x += refPt.x;
                    y += refPt.y;
                }
                if (doUpdateBounds) updateBounds(x, y);
                return { x, y };
            }

            // 직교 좌표: (x, y)
            const m = coordStr.match(/\(\s*(-?[\d.]+[a-zA-Z%]*)\s*,\s*(-?[\d.]+[a-zA-Z%]*)\s*\)/);
            if (m) {
                const xVal = m[1];
                const yVal = m[2];
                const hasXUnit = /[a-zA-Z%]/.test(xVal.replace(/^-?[\d.]+/, ''));
                const hasYUnit = /[a-zA-Z%]/.test(yVal.replace(/^-?[\d.]+/, ''));
                let x = (hasXUnit ? parseUnit(xVal, scaleX) : parseFloat(xVal) * scaleX);
                let y = -(hasYUnit ? parseUnit(yVal, scaleY) : parseFloat(yVal) * scaleY);
                if (refPt) {
                    x += refPt.x;
                    y += refPt.y;
                }
                if (doUpdateBounds) updateBounds(x, y);
                return { x, y };
            }
            return null;
        }

        const knownColors = [
            'red', 'blue', 'green', 'yellow', 'orange', 'purple', 'violet',
            'cyan', 'magenta', 'gray', 'darkgray', 'brown', 'pink', 'black',
            'teal', 'olive', 'lime'
        ];

        // Semicolon 분리 (단, 중괄호 {} 내부의 세미콜론은 분리하지 않음)
        const statements = [];
        let curStmt = '';
        let braceDepth = 0;
        for (let i = 0; i < body.length; i++) {
            const ch = body[i];
            if (ch === '{') braceDepth++;
            else if (ch === '}') braceDepth--;
            if (ch === ';' && braceDepth === 0) {
                if (curStmt.trim()) statements.push(curStmt.trim());
                curStmt = '';
            } else {
                curStmt += ch;
            }
        }
        if (curStmt.trim()) statements.push(curStmt.trim());

        statements.forEach(stmt => {
            stmt = stmt.trim();
            if (!stmt) return;

            // 1. \coordinate (A) at (x,y);
            const coordDefMatch = stmt.match(/^\\?coordinate\s*(?:\[[^\]]*\])?\s*\(([a-zA-Z0-9_\-]+)\)\s*at\s*(\([^\)]+\))/i);
            if (coordDefMatch) {
                const pt = parseCoord(coordDefMatch[2], null, false);
                if (pt) {
                    namedCoords.set(coordDefMatch[1], pt);
                }
                return;
            }

            let stroke = 'currentColor';
            let fill = 'none';
            let strokeWidth = 1.4; // 1em 기준 가독성 좋은 선 두께
            let strokeDash = '';
            let markerStart = '';
            let markerEnd = '';

            const cmdMatch = stmt.match(/^\\?(?:draw|fill|filldraw|node)\s*(?:\[([^\]]+)\])?/i);
            const options = cmdMatch && cmdMatch[1] ? cmdMatch[1] : '';

            // 색상 감지
            for (const col of knownColors) {
                if (options.includes(col)) {
                    stroke = col;
                    usedColors.add(col);
                    if (stmt.startsWith('\\fill')) fill = col;
                    break;
                }
            }

            // fill= 및 draw= 명시 옵션
            const fillOptMatch = options.match(/fill\s*=\s*([a-zA-Z0-9_#]+)/);
            if (fillOptMatch) {
                fill = fillOptMatch[1];
                usedColors.add(fill);
            } else if (stmt.startsWith('\\fill') && fill === 'none') {
                fill = stroke !== 'currentColor' ? stroke : '#bbb';
            }

            const drawOptMatch = options.match(/draw\s*=\s*([a-zA-Z0-9_#]+)/);
            if (drawOptMatch) {
                stroke = drawOptMatch[1];
                usedColors.add(stroke);
            }

            if (options.includes('ultra thin')) strokeWidth = 0.5;
            else if (options.includes('very thin')) strokeWidth = 0.8;
            else if (options.includes('thin')) strokeWidth = 1.1;
            else if (options.includes('semithick')) strokeWidth = 1.8;
            else if (options.includes('thick')) strokeWidth = 2.4;
            else if (options.includes('very thick')) strokeWidth = 3.2;
            else if (options.includes('ultra thick')) strokeWidth = 4.2;

            if (options.includes('dashed')) strokeDash = 'stroke-dasharray="5,5"';
            if (options.includes('dotted')) strokeDash = 'stroke-dasharray="2,2"';

            const markerCol = stroke === 'currentColor' ? 'black' : stroke;
            usedColors.add(markerCol);
            const markerUrl = `${svgId}-arrow-${markerCol}`;

            if (options.includes('<->')) {
                markerStart = `marker-start="url(#${markerUrl})"`;
                markerEnd = `marker-end="url(#${markerUrl})"`;
            } else if (options.includes('->') || options.includes('-latex')) {
                markerEnd = `marker-end="url(#${markerUrl})"`;
            } else if (options.includes('<-') || options.includes('latex-')) {
                markerStart = `marker-start="url(#${markerUrl})"`;
            }

            // shorten 옵션
            let shortenStart = 0;
            let shortenEnd = 0;
            const shortenStartMatch = options.match(/shorten\s*<\s*=\s*([^,\]]+)/);
            if (shortenStartMatch) shortenStart = parseUnit(shortenStartMatch[1], 0);
            const shortenEndMatch = options.match(/shorten\s*>\s*=\s*([^,\]]+)/);
            if (shortenEndMatch) shortenEnd = parseUnit(shortenEndMatch[1], 0);
            const shortenBothMatch = options.match(/\bshorten\s*=\s*([^,\]]+)/);
            if (shortenBothMatch) {
                shortenStart = parseUnit(shortenBothMatch[1], 0);
                shortenEnd = shortenStart;
            }

            // 좌표 추출
            const rawCoordMatches = stmt.match(/\(\s*-?[\d.]+[a-zA-Z%]*\s*,\s*-?[\d.]+[a-zA-Z%]*\s*\)|\([a-zA-Z0-9_\-]+\)|\(\s*-?[\d.]+\s*:\s*-?[\d.]+[a-zA-Z%]*\s*\)/g) || [];
            const pathCoords = rawCoordMatches.map(c => parseCoord(c)).filter(p => p !== null);

            // 2. node 파싱 (단독 \node 또는 경로 상의 -- node[...] {label} --)
            function findMatchingBrace(str, startIndex) {
                let depth = 0;
                let openIdx = -1;
                for (let i = startIndex; i < str.length; i++) {
                    if (str[i] === '{') {
                        if (depth === 0) openIdx = i;
                        depth++;
                    } else if (str[i] === '}') {
                        depth--;
                        if (depth === 0 && openIdx !== -1) {
                            return { open: openIdx, close: i, content: str.substring(openIdx + 1, i) };
                        }
                    }
                }
                return null;
            }

            const nodeRegex = /(?:\\node|node)\s*(?:\[([^\]]*)\])?\s*(?:\([^\)]*\))?\s*(?:at\s*(\([^\)]+\)))?/g;
            let nodeMatch;
            let inlineNodeFound = false;

            while ((nodeMatch = nodeRegex.exec(stmt)) !== null) {
                const braceInfo = findMatchingBrace(stmt, nodeRegex.lastIndex);
                if (!braceInfo) continue;
                nodeRegex.lastIndex = braceInfo.close + 1;

                inlineNodeFound = true;
                const nodeOpts = nodeMatch[1] || '';
                let pt = null;

                let isPathNode = false;
                if (nodeMatch[2]) {
                    pt = parseCoord(nodeMatch[2]);
                } else if (pathCoords.length >= 2) {
                    isPathNode = true;
                    let posRatio = 0.5;
                    const posMatch = nodeOpts.match(/pos\s*=\s*([\d.]+)/);
                    if (posMatch) posRatio = parseFloat(posMatch[1]);
                    else if (nodeOpts.includes('at start')) posRatio = 0.0;
                    else if (nodeOpts.includes('at end')) posRatio = 1.0;
                    else if (nodeOpts.includes('near start')) posRatio = 0.25;
                    else if (nodeOpts.includes('near end')) posRatio = 0.75;

                    const pStart = pathCoords[0];
                    const pEnd = pathCoords[pathCoords.length - 1];
                    pt = {
                        x: pStart.x + (pEnd.x - pStart.x) * posRatio,
                        y: pStart.y + (pEnd.y - pStart.y) * posRatio
                    };
                } else if (pathCoords.length > 0) {
                    pt = pathCoords[pathCoords.length - 1];
                }

                if (pt) {
                    let rawLabel = braceInfo.content.trim();
                    let offsetX = 0;
                    let offsetY = 0;

                    if (nodeOpts.includes('above')) offsetY -= 0.55 * EM;
                    if (nodeOpts.includes('below')) offsetY += 0.55 * EM;
                    if (nodeOpts.includes('left')) offsetX -= 0.65 * EM;
                    if (nodeOpts.includes('right')) offsetX += 0.65 * EM;

                    const xshiftMatch = nodeOpts.match(/xshift\s*=\s*([^,\]]+)/);
                    const yshiftMatch = nodeOpts.match(/yshift\s*=\s*([^,\]]+)/);
                    if (xshiftMatch) offsetX += parseUnit(xshiftMatch[1], scaleX);
                    if (yshiftMatch) offsetY -= parseUnit(yshiftMatch[1], scaleY);

                    const finalX = pt.x + offsetX;
                    const finalY = pt.y + offsetY;

                    // 라벨 크기에 맞춘 컴팩트한 바운딩 박스 계산 (과도한 상단/좌측 여백 방지)
                    const cleanLabel = rawLabel.replace(/\$|\\mathrm|\\scriptstyle|\\mathbf|\\mathit|\{|\}/g, '').trim();
                    const charCount = Math.max(1, cleanLabel.length);
                    const halfW = Math.min(45, Math.max(8, charCount * 4.5 + 4));
                    const halfH = 9;
                    updateBounds(finalX - halfW, finalY - halfH);
                    updateBounds(finalX + halfW, finalY + halfH);

                    // 수식 $...$ 가 포함된 경우 KaTeX로 수식 변환
                    let processedLabel = rawLabel;
                    if (typeof katex !== 'undefined' && /\$([\s\S]+?)\$/.test(rawLabel)) {
                        processedLabel = rawLabel.replace(/\$([\s\S]+?)\$/g, (m, math) => {
                            try {
                                return katex.renderToString(math, { displayMode: false, throwOnError: false });
                            } catch (e) {
                                return m;
                            }
                        });
                    }

                    const fontSize = isPathNode ? '0.9em' : '1em';
                    svgElements.push(`
                    <foreignObject x="${finalX - 60}" y="${finalY - 20}" width="120" height="40" style="overflow:visible; pointer-events:none;">
                        <div xmlns="http://www.w3.org/1999/xhtml" style="display:flex; justify-content:center; align-items:center; width:100%; height:100%; font-size:${fontSize}; color:${stroke === 'currentColor' ? 'var(--color-z)' : stroke}; line-height:1; font-family:'Pretendard',serif;">
                            ${processedLabel}
                        </div>
                    </foreignObject>`);
                }
            }

            if (stmt.startsWith('\\node') && inlineNodeFound) {
                return;
            }

            // 3. grid: (x1, y1) grid (x2, y2)
            if (stmt.includes('grid')) {
                const gridMatch = stmt.match(/(\([^\)]+\))\s*grid\s*(?:\[[^\]]*\])?\s*(\([^\)]+\))/);
                if (gridMatch) {
                    const p1 = parseCoord(gridMatch[1]);
                    const p2 = parseCoord(gridMatch[2]);
                    if (p1 && p2) {
                        const stepMatch = options.match(/step\s*=\s*([^,\]]+)/);
                        const stepPx = stepMatch ? parseUnit(stepMatch[1], scaleX) : (1 * EM);
                        const minGridX = Math.min(p1.x, p2.x);
                        const maxGridX = Math.max(p1.x, p2.x);
                        const minGridY = Math.min(p1.y, p2.y);
                        const maxGridY = Math.max(p1.y, p2.y);

                        let gridLines = '';
                        for (let gx = minGridX; gx <= maxGridX + 0.1; gx += stepPx) {
                            gridLines += `<line x1="${gx}" y1="${minGridY}" x2="${gx}" y2="${maxGridY}" stroke="${stroke}" stroke-width="${strokeWidth}" ${strokeDash} />`;
                        }
                        for (let gy = minGridY; gy <= maxGridY + 0.1; gy += stepPx) {
                            gridLines += `<line x1="${minGridX}" y1="${gy}" x2="${maxGridX}" y2="${gy}" stroke="${stroke}" stroke-width="${strokeWidth}" ${strokeDash} />`;
                        }
                        updateBounds(minGridX, minGridY);
                        updateBounds(maxGridX, maxGridY);
                        svgElements.push(`<g opacity="0.45">${gridLines}</g>`);
                        return;
                    }
                }
            }

            // 4. circle: (x, y) circle (r) 또는 circle [radius=r]
            if (stmt.includes('circle')) {
                const circleMatch = stmt.match(/(\([^\)]+\))\s*circle\s*(?:\(\s*([^)]+)\s*\)|\[\s*radius\s*=\s*([^\]]+)\s*\])/);
                if (circleMatch) {
                    const pt = parseCoord(circleMatch[1]);
                    const rStr = circleMatch[2] || circleMatch[3];
                    const r = parseUnit(rStr, scaleX);
                    if (pt) {
                        updateBounds(pt.x - r, pt.y - r);
                        updateBounds(pt.x + r, pt.y + r);
                        svgElements.push(`<circle cx="${pt.x}" cy="${pt.y}" r="${r}" stroke="${stroke}" stroke-width="${strokeWidth}" fill="${fill}" ${strokeDash} stroke-linecap="round" stroke-linejoin="round" />`);
                        return;
                    }
                }
            }

            // 5. ellipse: (x, y) ellipse (rx and ry)
            if (stmt.includes('ellipse')) {
                const ellipseMatch = stmt.match(/(\([^\)]+\))\s*ellipse\s*\(\s*([^)]+?)\s+and\s+([^)]+?)\s*\)/);
                if (ellipseMatch) {
                    const pt = parseCoord(ellipseMatch[1]);
                    const rx = parseUnit(ellipseMatch[2], scaleX);
                    const ry = parseUnit(ellipseMatch[3], scaleY);
                    if (pt) {
                        updateBounds(pt.x - rx, pt.y - ry);
                        updateBounds(pt.x + rx, pt.y + ry);
                        svgElements.push(`<ellipse cx="${pt.x}" cy="${pt.y}" rx="${rx}" ry="${ry}" stroke="${stroke}" stroke-width="${strokeWidth}" fill="${fill}" ${strokeDash} stroke-linecap="round" stroke-linejoin="round" />`);
                        return;
                    }
                }
            }

            // 6. rectangle: (x1, y1) rectangle (x2, y2)
            if (stmt.includes('rectangle')) {
                const rectMatch = stmt.match(/(\([^\)]+\))\s*rectangle\s*(\([^\)]+\))/);
                if (rectMatch) {
                    const p1 = parseCoord(rectMatch[1]);
                    const p2 = parseCoord(rectMatch[2]);
                    if (p1 && p2) {
                        const rx = Math.min(p1.x, p2.x);
                        const ry = Math.min(p1.y, p2.y);
                        const rw = Math.abs(p1.x - p2.x);
                        const rh = Math.abs(p1.y - p2.y);
                        updateBounds(rx, ry);
                        updateBounds(rx + rw, ry + rh);
                        svgElements.push(`<rect x="${rx}" y="${ry}" width="${rw}" height="${rh}" stroke="${stroke}" stroke-width="${strokeWidth}" fill="${fill}" ${strokeDash} stroke-linecap="round" stroke-linejoin="round" />`);
                        return;
                    }
                }
            }

            // 7. arc: (x, y) arc (start:end:radius)
            if (stmt.includes('arc')) {
                const arcMatch = stmt.match(/(\([^\)]+\))\s*arc\s*\(\s*(-?[\d.]+)\s*:\s*(-?[\d.]+)\s*:\s*([^)]+)\s*\)/);
                if (arcMatch) {
                    const startPt = parseCoord(arcMatch[1]);
                    const startAngle = parseFloat(arcMatch[2]);
                    const endAngle = parseFloat(arcMatch[3]);
                    const r = parseUnit(arcMatch[4], scaleX);
                    if (startPt) {
                        const startRad = (startAngle * Math.PI) / 180;
                        const endRad = (endAngle * Math.PI) / 180;
                        const centerX = startPt.x - r * Math.cos(startRad);
                        const centerY = startPt.y + r * Math.sin(startRad);
                        const endX = centerX + r * Math.cos(endRad);
                        const endY = centerY - r * Math.sin(endRad);

                        updateBounds(startPt.x, startPt.y);
                        updateBounds(endX, endY);
                        // 호(Arc)를 따라 실제 점들을 샘플링하여 정확한 바운딩 박스 계산 (원 전체 확장 방지)
                        const arcSteps = 8;
                        for (let s = 1; s < arcSteps; s++) {
                            const a = startAngle + (endAngle - startAngle) * (s / arcSteps);
                            const aRad = (a * Math.PI) / 180;
                            const ax = centerX + r * Math.cos(aRad);
                            const ay = centerY - r * Math.sin(aRad);
                            updateBounds(ax, ay);
                        }

                        const angleDiff = Math.abs(endAngle - startAngle);
                        const largeArc = angleDiff > 180 ? 1 : 0;
                        const sweep = endAngle > startAngle ? 0 : 1;

                        const arcPath = `M ${startPt.x} ${startPt.y} A ${r} ${r} 0 ${largeArc} ${sweep} ${endX} ${endY}`;
                        svgElements.push(`<path d="${arcPath}" stroke="${stroke}" stroke-width="${strokeWidth}" fill="${fill}" ${strokeDash} stroke-linecap="round" stroke-linejoin="round" ${markerStart} ${markerEnd} />`);
                        return;
                    }
                }
            }

            // 8. plot: plot[domain=min:max] (\x, {expr})
            if (stmt.includes('plot')) {
                const domainMatch = stmt.match(/domain\s*=\s*(-?[\d.]+)\s*:\s*(-?[\d.]+)/);
                const minDomain = domainMatch ? parseFloat(domainMatch[1]) : -2;
                const maxDomain = domainMatch ? parseFloat(domainMatch[2]) : 2;

                const exprMatch = stmt.match(/plot\s*(?:\[[^\]]*\])?\s*\(\s*\\?x\s*,\s*\{?([^}]+)\}?\s*\)/i);
                const rawExpr = exprMatch ? exprMatch[1].trim() : 'x^2';

                function evalExpr(xVal, expr) {
                    let jsExpr = expr
                        .replace(/\\x/g, 'x')
                        .replace(/x\^3/g, 'Math.pow(x,3)')
                        .replace(/x\^2/g, 'Math.pow(x,2)')
                        .replace(/x\^([\d.]+)/g, 'Math.pow(x,$1)')
                        .replace(/sin\(x\)/g, 'Math.sin(x)')
                        .replace(/cos\(x\)/g, 'Math.cos(x)')
                        .replace(/tan\(x\)/g, 'Math.tan(x)')
                        .replace(/sqrt\(x\)/g, 'Math.sqrt(x)')
                        .replace(/exp\(x\)/g, 'Math.exp(x)')
                        .replace(/ln\(x\)/g, 'Math.log(x)');

                    jsExpr = jsExpr.replace(/(\d+)\s*x/g, '$1*x');

                    try {
                        return Function('x', 'return ' + jsExpr)(xVal);
                    } catch (e) {
                        return 0;
                    }
                }

                const samples = 100;
                const step = (maxDomain - minDomain) / samples;
                const plotPoints = [];

                for (let i = 0; i <= samples; i++) {
                    const xVal = minDomain + i * step;
                    const yVal = evalExpr(xVal, rawExpr);
                    if (!isNaN(yVal) && isFinite(yVal)) {
                        const pt = parseCoord(`(${xVal}, ${yVal})`);
                        if (pt) plotPoints.push(pt);
                    }
                }

                if (plotPoints.length >= 2) {
                    const pointsStr = plotPoints.map(p => `${p.x.toFixed(2)},${p.y.toFixed(2)}`).join(' ');
                    svgElements.push(`<polyline points="${pointsStr}" stroke="${stroke}" stroke-width="${strokeWidth}" fill="none" ${strokeDash} stroke-linecap="round" stroke-linejoin="round" ${markerStart} ${markerEnd} />`);
                    return;
                }
            }

            // 9. Polyline & Polygon (-- 및 -- cycle)
            if (pathCoords.length >= 2) {
                let pts = pathCoords.map(p => ({ x: p.x, y: p.y }));
                if (pts.length >= 2 && (shortenStart > 0 || shortenEnd > 0)) {
                    if (shortenStart > 0) {
                        const dx = pts[1].x - pts[0].x;
                        const dy = pts[1].y - pts[0].y;
                        const d = Math.sqrt(dx * dx + dy * dy);
                        if (d > shortenStart) {
                            pts[0].x += (dx / d) * shortenStart;
                            pts[0].y += (dy / d) * shortenStart;
                        }
                    }
                    if (shortenEnd > 0) {
                        const last = pts.length - 1;
                        const dx = pts[last].x - pts[last - 1].x;
                        const dy = pts[last].y - pts[last - 1].y;
                        const d = Math.sqrt(dx * dx + dy * dy);
                        if (d > shortenEnd) {
                            pts[last].x -= (dx / d) * shortenEnd;
                            pts[last].y -= (dy / d) * shortenEnd;
                        }
                    }
                }

                const pointsStr = pts.map(p => `${p.x.toFixed(1)},${p.y.toFixed(1)}`).join(' ');
                if (stmt.includes('cycle')) {
                    svgElements.push(`<polygon points="${pointsStr}" stroke="${stroke}" stroke-width="${strokeWidth}" fill="${fill}" ${strokeDash} stroke-linecap="round" stroke-linejoin="round" />`);
                } else {
                    svgElements.push(`<polyline points="${pointsStr}" stroke="${stroke}" stroke-width="${strokeWidth}" fill="${fill}" ${strokeDash} stroke-linecap="round" stroke-linejoin="round" ${markerStart} ${markerEnd} />`);
                }
            }
        });

        if (minX === Infinity || !svgElements.length) {
            return '';
        }

        // 여백: 스트로크 및 화살표 마커가 잘리지 않는 최소 안전 여백(4px) 설정
        const padding = 4;
        const svgWidth = Math.ceil(maxX - minX + padding * 2);
        const svgHeight = Math.ceil(maxY - minY + padding * 2);
        const viewBox = `${(minX - padding).toFixed(1)} ${(minY - padding).toFixed(1)} ${svgWidth} ${svgHeight}`;

        const markerDefs = Array.from(usedColors).map(col => `
            <marker id="${svgId}-arrow-${col}" viewBox="0 -520 1000 520" refX="943" refY="-250" markerWidth="24" markerHeight="14" orient="auto">
                <g transform="scale(1,-1)">
                    <path d="M932 234C939 237 943 243 943 250C943 257 939 263 932 266C884 282 839 316 797 368C769 403 750 444 741 491C738 504 730 510 717 510C701 510 693 502 693 485L694 483L694 482C711 395 755 326 828 274L828 226C755 174 711 105 694 18L694 17L693 15C693-2 701-10 717-10C730-10 738-4 741 9C750 56 769 97 797 132C839 184 884 218 932 234Z" fill="${col === 'currentColor' ? 'black' : col}" />
                </g>
            </marker>
        `).join('\n');

        const widthEm = (svgWidth / EM).toFixed(3);
        const heightEm = (svgHeight / EM).toFixed(3);

        return `<svg xmlns="http://www.w3.org/2000/svg" width="${widthEm}em" height="${heightEm}em" viewBox="${viewBox}" style="display:block;margin:0;overflow:visible;"><defs>${markerDefs.trim()}</defs>${svgElements.join('')}</svg>`;
    }

    function renderTikzToHtml(tikz) {
        if (!tikz) return '';
        const svg = convertTikzToSvg(tikz);
        if (svg) return svg.trim();
        return `<span class="graph-empty-placeholder">[그래프...]</span>`;
    }

    function parseBalancedBlock(str, startIdx, openChar = '{', closeChar = '}') {
        if (startIdx >= str.length || str[startIdx] !== openChar) return null;
        let depth = 1;
        let i = startIdx + 1;
        while (i < str.length && depth > 0) {
            if (str[i] === openChar) depth++;
            else if (str[i] === closeChar) depth--;
            i++;
        }
        if (depth === 0) {
            return {
                content: str.substring(startIdx + 1, i - 1),
                nextIndex: i
            };
        }
        return null;
    }

    function replaceTextCommand(html, cmdName, openTag, closeTag) {
        let searchStr = '\\' + cmdName + '{';
        let idx = 0;
        let safety = 0;

        while (safety < 1000) {
            safety++;
            idx = html.indexOf(searchStr, idx);
            if (idx === -1) break;

            let openBraceIdx = idx + searchStr.length - 1;
            let block = parseBalancedBlock(html, openBraceIdx, '{', '}');
            if (block) {
                let before = html.substring(0, idx);
                let innerContent = block.content;
                let after = html.substring(block.nextIndex);

                let transformedInner = replaceTextCommand(innerContent, cmdName, openTag, closeTag);
                let replacement = openTag + transformedInner + closeTag;

                html = before + replacement + after;
                idx = before.length + replacement.length;
            } else {
                idx += searchStr.length;
            }
        }
        return html;
    }

    function parseMathToHtml(rawText) {
        if (!rawText) return '';
        let text = rawText;

        // 1. 기존 데이터에 혹시 남아있을 수 있는 HTML 엔티티 이중 인코딩 정제
        text = text
            .replace(/&amp;lt;/g, '<')
            .replace(/&amp;gt;/g, '>')
            .replace(/&amp;amp;/g, '&')
            .replace(/&lt;/g, '<')
            .replace(/&gt;/g, '>')
            .replace(/&amp;/g, '&');

        // 기존 데이터에 포함된 HTML 서식 태그를 \textbf / \textit / \underline으로 정규화
        text = text
            .replace(/<(?:strong|b)>(.*?)<\/(?:strong|b)>/gi, '\\textbf{$1}')
            .replace(/<(?:em|i)>(.*?)<\/(?:em|i)>/gi, '\\textit{$1}')
            .replace(/<u>(.*?)<\/u>/gi, '\\underline{$1}')
            .replace(/<\/?p\b[^>]*>/gi, '')
            .replace(/<\/?div\b[^>]*>/gi, '');

        // 1-b. TikZ 그래프 블록 (\begin{tikzpicture}...\end{tikzpicture})을 안전하게 추출하여 토큰으로 마스킹
        const tikzTokens = [];
        text = text.replace(/\\begin\{tikzpicture\}([\s\S]*?)\\end\{tikzpicture\}/gi, (match, body) => {
            const cleanTikz = body.trim();
            const rendered = renderTikzToHtml(cleanTikz);
            const token = `___TIKZ_TOKEN_${tikzTokens.length}___`;
            tikzTokens.push(`<span class="inline-graph" data-tikz="${escapeHtmlAttr(cleanTikz)}" contenteditable="false">${rendered.trim()}</span>`);
            return token;
        });

        // 2. 수식 블록 ($$...$$ 및 $...$)을 안전하게 추출하여 토큰으로 마스킹
        const mathTokens = [];

        // $$...$$ (디스플레이 수식)
        text = text.replace(/(?<!\\)\$\$([\s\S]*?)(?<!\\)\$\$/g, (match, math) => {
            const cleanMath = math.trim();
            const rendered = renderLatexToHtml(cleanMath, false);
            const token = `___MATH_TOKEN_${mathTokens.length}___`;
            mathTokens.push(`<span class="inline-math" data-latex="${escapeHtmlAttr(cleanMath)}" contenteditable="false">${rendered}</span>`);
            return token;
        });

        // $...$ (인라인 수식)
        text = text.replace(/(?<!\\)\$(?!\$)([\s\S]*?)(?<!\\)\$/g, (match, math) => {
            const cleanMath = math.trim();
            const rendered = renderLatexToHtml(cleanMath, false);
            const token = `___MATH_TOKEN_${mathTokens.length}___`;
            mathTokens.push(`<span class="inline-math" data-latex="${escapeHtmlAttr(cleanMath)}" contenteditable="false">${rendered}</span>`);
            return token;
        });


        // 3. 줄바꿈 태그(<br>, <br/>) 보호 및 \r\n 중복 폭증 원천 차단
        text = text.replace(/<br\s*\/?>\s*\r?\n/gi, '<br>');
        text = text.replace(/\r?\n\s*<br\s*\/?>/gi, '<br>');
        text = text.replace(/\r?\n/g, '<br>');
        // 3개 이상 연속된 <br>은 최대 2개(<br><br> = 빈 줄 1개)로 정규화
        text = text.replace(/(?:<br\s*\/?>){3,}/gi, '<br><br>');

        const BR_TOKEN = '___SAFE_BR_TOKEN___';
        text = text.replace(/<br\s*\/?>/gi, BR_TOKEN);

        // 4. 일반 텍스트 내의 특수문자(<, >, &)를 안전하게 HTML 엔티티로 변환
        // (브라우저가 '<'를 HTML 태그 시작으로 오인하여 삼켜버리거나 태그를 왜곡하는 문제 원천 차단)
        text = text
            .replace(/&/g, '&amp;')
            .replace(/</g, '&lt;')
            .replace(/>/g, '&gt;');

        // 5. 텍스트 서식 명령어 (\textbf{}, \textit{}, \underline{})를 HTML 태그로 변환
        text = replaceTextCommand(text, 'textbf', '<b>', '</b>');
        text = replaceTextCommand(text, 'textit', '<i>', '</i>');
        text = replaceTextCommand(text, 'underline', '<u>', '</u>');

        // 6. 목록 환경 (\begin{itemize})을 글머리 기호 flex 블록으로 변환
        const itemizeRegex = /\\begin\{itemize\}(?:\s*\[([^\]]*)\])?([\s\S]*?)\\end\{itemize\}/gi;
        let itemizePass = 0;
        while (itemizeRegex.test(text) && itemizePass < 10) {
            itemizePass++;
            text = text.replace(itemizeRegex, (_, optionsStr, body) => {
                return parseItemizeBodyToHtml(body, BR_TOKEN, optionsStr);
            });
        }

        // 7. BR_TOKEN으로 나눈 줄들을 문단 블록(<p> 또는 .bullet-item)으로 포장
        const rawLines = text.split(BR_TOKEN);
        const blockHtmlList = [];

        rawLines.forEach(line => {
            let trimmed = line.trim();
            if (!trimmed) {
                // 빈 줄: 브라우저가 높이를 렌더링하고 커서가 깜빡일 수 있도록 <br>이 포함된 <p>
                blockHtmlList.push('<p><br></p>');
            } else if (trimmed.startsWith('<div class="bullet-item"')) {
                // 이미 글머리 기호 블록인 경우 그대로 추가
                blockHtmlList.push(trimmed);
            } else {
                let align = '';
                let padding = '';
                let content = trimmed;

                // 1. 외곽 정렬 환경 검사 (\begin{center}, \begin{flushright})
                const centerMatch = content.match(/^\\begin\{center\}([\s\S]*?)\\end\{center\}$/i);
                const rightMatch = content.match(/^\\begin\{flushright\}([\s\S]*?)\\end\{flushright\}$/i);

                if (centerMatch) {
                    align = 'center';
                    content = centerMatch[1].trim();
                } else if (rightMatch) {
                    align = 'right';
                    content = rightMatch[1].trim();
                }

                // 2. 들여쓰기 환경 검사 (\begin{leftskip}[len], \begin{tab}[len])
                const leftskipMatch = content.match(/^\\begin\{(?:leftskip|tab)\}(?:\s*\[([^\]]*)\])?([\s\S]*?)\\end\{(?:leftskip|tab)\}$/i);
                if (leftskipMatch) {
                    let pad = (leftskipMatch[1] || '1em').trim();
                    if (/^[0-9.]+$/.test(pad)) pad += 'em';
                    padding = pad;
                    content = leftskipMatch[2].trim();
                }

                // 3. 만약 leftskip 안에 center/flushright가 중첩된 경우 처리
                if (!align) {
                    const innerCenter = content.match(/^\\begin\{center\}([\s\S]*?)\\end\{center\}$/i);
                    const innerRight = content.match(/^\\begin\{flushright\}([\s\S]*?)\\end\{flushright\}$/i);
                    if (innerCenter) {
                        align = 'center';
                        content = innerCenter[1].trim();
                    } else if (innerRight) {
                        align = 'right';
                        content = innerRight[1].trim();
                    }
                }

                let margin = '';
                // \vspace{...} 검사
                const vspaceMatch = content.match(/\\vspace\{([+-]?[0-9.]+(?:em|px)?)\}/i);
                if (vspaceMatch) {
                    let m = vspaceMatch[1].trim();
                    if (/^[+-]?[0-9.]+$/.test(m)) m += 'em';
                    margin = m;
                    content = content.replace(/\\vspace\{[+-]?[0-9.]+(?:em|px)?\}/i, '').trim();
                }

                // \\[...em] 줄바꿈 간격이 끝에 있는 경우 검사
                const newlineSpacingMatch = content.match(/\\\\\[([+-]?[0-9.]+(?:em|px)?)\s*\]\s*$/i);
                if (newlineSpacingMatch) {
                    if (!margin) {
                        let m = newlineSpacingMatch[1].trim();
                        if (/^[+-]?[0-9.]+$/.test(m)) m += 'em';
                        margin = m;
                    }
                    content = content.replace(/\\\\\[[+-]?[0-9.]+(?:em|px)?\s*\]\s*$/i, '').trim();
                }

                let pContent = content.replace(/\\\\(?:\s*\[[^\]]*\])?/g, '<br>');
                const styles = [];
                if (align) styles.push(`text-align: ${align};`);
                if (padding) styles.push(`padding-left: ${padding};`);
                if (margin) styles.push(`margin-bottom: ${margin};`);
                const styleAttr = styles.length > 0 ? ` style="${styles.join(' ')}"` : '';

                blockHtmlList.push(`<p${styleAttr}>${pContent || '<br>'}</p>`);
            }
        });

        let resultHtml = blockHtmlList.length > 0 ? blockHtmlList.join('') : '<p><br></p>';

        // 8. 마스킹했던 KaTeX 수식 HTML 스팬 및 TikZ 그래프 복원
        mathTokens.forEach((renderedHtml, idx) => {
            const token = `___MATH_TOKEN_${idx}___`;
            resultHtml = resultHtml.split(token).join(renderedHtml);
        });
        tikzTokens.forEach((renderedHtml, idx) => {
            const token = `___TIKZ_TOKEN_${idx}___`;
            resultHtml = resultHtml.split(token).join(renderedHtml);
        });

        return resultHtml;
    }

    function parseItemizeBodyToHtml(body, brToken, optionsStr = '') {
        const itemRegex = /\\item(?![a-zA-Z])/g;
        const itemIndices = [];
        let match;
        while ((match = itemRegex.exec(body)) !== null) {
            itemIndices.push(match.index);
        }
        if (itemIndices.length === 0) {
            return body;
        }

        let defaultLeft = '';
        if (optionsStr) {
            const m = optionsStr.match(/left\s*=\s*([0-9.]+(?:em|px)?)/i);
            if (m) {
                defaultLeft = m[1];
                if (!defaultLeft.endsWith('em') && !defaultLeft.endsWith('px')) defaultLeft += 'em';
            }
        }

        let leadContent = body.substring(0, itemIndices[0]).trim();
        let result = leadContent ? `<p>${leadContent}</p>` : '';

        for (let k = 0; k < itemIndices.length; k++) {
            const startIdx = itemIndices[k];
            const nextStartIdx = (k + 1 < itemIndices.length) ? itemIndices[k + 1] : body.length;

            let cursor = startIdx + 5; // length of '\item'
            while (cursor < nextStartIdx && /\s/.test(body[cursor])) {
                cursor++;
            }

            let customLabel = '•';
            let itemLeft = null;
            let itemMargin = null;

            // 대괄호 옵션들 순차 검사 ([label], [left=...], [margin=...])
            while (cursor < nextStartIdx && body[cursor] === '[') {
                const closeBracket = body.indexOf(']', cursor);
                if (closeBracket === -1 || closeBracket >= nextStartIdx) break;
                const bracketContent = body.substring(cursor + 1, closeBracket).trim();
                const leftMatch = bracketContent.match(/^left\s*=\s*([0-9.]+(?:em|px)?)$/i);
                const marginMatch = bracketContent.match(/^margin(?:-bottom)?\s*=\s*([+-]?[0-9.]+(?:em|px)?)$/i);
                if (leftMatch) {
                    itemLeft = leftMatch[1];
                    if (!itemLeft.endsWith('em') && !itemLeft.endsWith('px')) itemLeft += 'em';
                } else if (marginMatch) {
                    itemMargin = marginMatch[1];
                    if (!itemMargin.endsWith('em') && !itemMargin.endsWith('px')) itemMargin += 'em';
                } else {
                    customLabel = bracketContent || '•';
                }
                cursor = closeBracket + 1;
                while (cursor < nextStartIdx && /\s/.test(body[cursor])) {
                    cursor++;
                }
            }

            let itemContent = body.substring(cursor, nextStartIdx).trim();
            while (itemContent.startsWith(brToken)) {
                itemContent = itemContent.substring(brToken.length).trim();
            }
            while (itemContent.endsWith(brToken)) {
                itemContent = itemContent.substring(0, itemContent.length - brToken.length).trim();
            }

            // \vspace{...} 검사
            const itemVspaceMatch = itemContent.match(/\\vspace\{([+-]?[0-9.]+(?:em|px)?)\}/i);
            if (itemVspaceMatch) {
                if (!itemMargin) {
                    let m = itemVspaceMatch[1].trim();
                    if (/^[+-]?[0-9.]+$/.test(m)) m += 'em';
                    itemMargin = m;
                }
                itemContent = itemContent.replace(/\\vspace\{[+-]?[0-9.]+(?:em|px)?\}/i, '').trim();
            }

            // soft break (\\) 변환 및 잔여 brToken 처리
            itemContent = itemContent.replace(/\\\\(?:\s*\[[^\]]*\])?/g, '<br>');
            itemContent = itemContent.split(brToken).join('<br>');

            if (!itemContent) itemContent = '<br>';

            const finalLeft = itemLeft || defaultLeft;
            const itemStyles = [];
            if (finalLeft) itemStyles.push(`padding-left: ${finalLeft};`);
            if (itemMargin) itemStyles.push(`margin-bottom: ${itemMargin};`);
            const styleAttr = itemStyles.length > 0 ? ` style="${itemStyles.join(' ')}"` : '';

            const itemBlock = `<div class="bullet-item"${styleAttr}><span class="bullet-marker" contenteditable="false">${escapeHtmlAttr(customLabel)}</span><div class="bullet-content">${itemContent}</div></div>`;
            result += itemBlock;
        }
        return result;
    }

    function cleanHtmlLineBreaks(html) {
        if (!html) return '';
        return html
            .replace(/<div><br\s*\/?>/gi, '<br>')
            .replace(/<div>/gi, '<br>')
            .replace(/<\/div>/gi, '')
            .replace(/<p><br\s*\/?>/gi, '<br>')
            .replace(/<p>/gi, '<br>')
            .replace(/<\/p>/gi, '')
            .replace(/\r?\n/g, '<br>')
            .replace(/&nbsp;|\u00a0/g, ' ');
    }

    function serializeHtmlToText(textEl) {
        if (!textEl) return '';

        function nodeToText(node) {
            if (node.nodeType === Node.TEXT_NODE) {
                return (node.nodeValue || '').replace(/\r?\n/g, ' ');
            }
            if (node.nodeType !== Node.ELEMENT_NODE) {
                return '';
            }

            const tag = node.tagName.toLowerCase();

            if (tag === 'br') {
                return '\\\\';
            }

            if (node.classList && node.classList.contains('inline-math')) {
                const latex = (node.dataset.latex || '').trim();
                return latex ? `$${latex}$` : '';
            }

            if (node.classList && node.classList.contains('inline-graph')) {
                const tikz = (node.dataset.tikz || '').trim();
                return tikz ? `\\begin{tikzpicture}\n${tikz}\n\\end{tikzpicture}` : '';
            }

            let inner = '';
            for (let child of node.childNodes) {
                inner += nodeToText(child);
            }

            if (!inner) return '';

            const isBold = tag === 'b' || tag === 'strong' || (node.style && (node.style.fontWeight === 'bold' || parseInt(node.style.fontWeight) >= 600));
            const isItalic = tag === 'i' || tag === 'em' || (node.style && node.style.fontStyle === 'italic');
            const isUnderline = tag === 'u' || (node.style && node.style.textDecoration && node.style.textDecoration.includes('underline'));

            let formatted = inner;
            if (isUnderline) {
                formatted = `\\underline{${formatted}}`;
            }
            if (isItalic) {
                formatted = `\\textit{${formatted}}`;
            }
            if (isBold) {
                formatted = `\\textbf{${formatted}}`;
            }

            return formatted;
        }

        function blockToText(blockNode) {
            if (!blockNode) return '';
            const textContent = (blockNode.textContent || '').trim();
            const hasMath = !!(blockNode.querySelector && blockNode.querySelector('.inline-math, .inline-graph'));
            if (!textContent && !hasMath) return '';

            const children = Array.from(blockNode.childNodes);
            let endIdx = children.length - 1;
            while (endIdx >= 0) {
                const last = children[endIdx];
                if (last.nodeType === Node.ELEMENT_NODE && last.tagName.toLowerCase() === 'br') {
                    endIdx--;
                } else {
                    break;
                }
            }

            let result = '';
            for (let i = 0; i <= endIdx; i++) {
                result += nodeToText(children[i]);
            }
            return result.trim();
        }

        const lines = [];

        for (let child of Array.from(textEl.childNodes)) {
            if (child.nodeType === Node.ELEMENT_NODE) {
                const tag = child.tagName.toLowerCase();

                if (tag === 'p' || (tag === 'div' && !child.classList.contains('bullet-item'))) {
                    const align = child.style.textAlign || '';
                    const padding = child.style.paddingLeft || '';
                    const margin = child.style.marginBottom || '';
                    const inner = blockToText(child);

                    // 빈 p인 경우 (내용이 없거나 오직 <br>만 있음) -> 빈 줄
                    if (!inner) {
                        lines.push('');
                    } else {
                        let pText = inner;
                        if (padding) {
                            pText = `\\begin{leftskip}[${padding}]${pText}\\end{leftskip}`;
                        }
                        if (margin) {
                            pText = `${pText} \\vspace{${margin}}`;
                        }
                        if (align === 'center') {
                            lines.push(`\\begin{center}${pText}\\end{center}`);
                        } else if (align === 'right') {
                            lines.push(`\\begin{flushright}${pText}\\end{flushright}`);
                        } else {
                            lines.push(pText);
                        }
                    }
                } else if (child.classList && child.classList.contains('bullet-item')) {
                    const markerEl = child.querySelector('.bullet-marker');
                    const marker = markerEl ? (markerEl.textContent || '').trim() : '•';
                    const contentEl = child.querySelector('.bullet-content');
                    const innerContent = blockToText(contentEl);
                    const labelPart = (marker && marker !== '•') ? `[${marker}]` : '';
                    const padding = child.style.paddingLeft ? `[left=${child.style.paddingLeft}]` : '';
                    const margin = child.style.marginBottom ? `[margin=${child.style.marginBottom}]` : '';
                    lines.push(`___BULLET_ITEM_START___\\item${labelPart}${padding}${margin} ${innerContent}___BULLET_ITEM_END___`);
                } else if (tag === 'br') {
                    lines.push('');
                } else {
                    let inlineText = nodeToText(child).trim();
                    if (inlineText) lines.push(inlineText);
                }
            } else if (child.nodeType === Node.TEXT_NODE) {
                const val = (child.nodeValue || '').trim();
                if (val) lines.push(val);
            }
        }

        // 연속된 빈 줄이 무한정 증식하지 않도록 최대 1개(=<br><br>)까지만 허용
        const cleanedLines = [];
        let prevEmpty = false;
        for (let l of lines) {
            const isEmpty = (l === '' || l === undefined || l === null);
            if (isEmpty) {
                if (!prevEmpty) {
                    cleanedLines.push('');
                    prevEmpty = true;
                }
            } else {
                cleanedLines.push(l);
                prevEmpty = false;
            }
        }

        let text = cleanedLines.join('<br>');

        // 연속된 bullet item들을 하나의 \begin{itemize} ... \end{itemize}로 완벽하게 그룹화
        text = text.replace(/(?:___BULLET_ITEM_START___[\s\S]*?___BULLET_ITEM_END___(?:\s*<br\s*\/?>\s*)?)+/g, (match) => {
            const rawItems = match
                .split('___BULLET_ITEM_START___')
                .join('')
                .split('___BULLET_ITEM_END___')
                .map(s => s.replace(/<br\s*\/?>/gi, '').trim())
                .filter(s => s.length > 0);
            return `\\begin{itemize}<br>${rawItems.join('<br>')}<br>\\end{itemize}`;
        });

        // 3개 이상 연속된 <br> 축소 및 텍스트 맨 앞/뒤 빈 줄 정제
        text = text.replace(/(?:<br\s*\/?>){3,}/gi, '<br><br>');
        text = text.replace(/^(?:<br\s*\/?>)+|(?:<br\s*\/?>)+$/gi, '');

        return text;
    }

    // =========================================================================
    // 3. 기하 및 영역 교차 판정 알고리즘 (Geometry & Intersection Utils)
    // =========================================================================
    function isBoxItemIntersecting(item, mLeft, mTop, mRight, mBottom) {
        const bLeft = item.left;
        const bTop = item.top;
        const bRight = bLeft + item.width;
        const bBottom = bTop + item.height;
        return !(bRight < mLeft || bLeft > mRight || bBottom < mTop || bTop > mBottom);
    }

    function isLineItemIntersecting(item, mLeft, mTop, mRight, mBottom) {
        const left = item.left;
        const top = item.top;
        const width = item.width;
        const height = item.height;

        if (isNaN(left) || isNaN(top) || isNaN(width) || isNaN(height)) return false;
        if (width === 0 && height === 0) return false;

        const x1 = left + 0.5;
        const y1 = top + 0.5;
        const x2 = x1 + width;
        const y2 = y1 + height;

        // 1. AABB 빠른 탈락 검사
        const minX = Math.min(x1, x2);
        const maxX = Math.max(x1, x2);
        const minY = Math.min(y1, y2);
        const maxY = Math.max(y1, y2);

        if (maxX < mLeft || minX > mRight || maxY < mTop || minY > mBottom) {
            return false;
        }

        // 2. 끝점이 사각형 내부에 있는 경우
        if ((x1 >= mLeft && x1 <= mRight && y1 >= mTop && y1 <= mBottom) ||
            (x2 >= mLeft && x2 <= mRight && y2 <= mTop && y2 <= mBottom)) {
            return true;
        }

        // 3. Liang-Barsky 알고리즘
        const dx = x2 - x1;
        const dy = y2 - y1;
        const p = [-dx, dx, -dy, dy];
        const q = [x1 - mLeft, mRight - x1, y1 - mTop, mBottom - y1];
        let u1 = 0.0;
        let u2 = 1.0;

        for (let i = 0; i < 4; i++) {
            if (p[i] === 0) {
                if (q[i] < 0) return false;
            } else {
                const t = q[i] / p[i];
                if (p[i] < 0) {
                    if (t > u2) return false;
                    if (t > u1) u1 = t;
                } else {
                    if (t < u1) return false;
                    if (t < u2) u2 = t;
                }
            }
        }

        return u1 <= u2;
    }

    // =========================================================================
    // 3. 뷰포트 & 그리드 관리자 (Viewport & Grid Manager)
    // =========================================================================
    class ViewportManager {
        constructor(gridEl, tooltipEl) {
            this.gridEl = gridEl;
            this.tooltipEl = tooltipEl;

            // 뷰포트 상태 변수
            this.panX = 0;
            this.panY = 0;
            this.scale = CONFIG.DEFAULT_SCALE;

            // 픽셀 및 크기 캐시
            this.cellSize = parseFloat(getComputedStyle(this.gridEl).fontSize) || CONFIG.DEFAULT_CELL_SIZE_PX;
            this.gridWidthEm = CONFIG.DEFAULT_GRID_SIZE_EM;
            this.gridHeightEm = CONFIG.DEFAULT_GRID_SIZE_EM;
            this.cachedViewWidth = window.innerWidth;
            this.cachedViewHeight = window.innerHeight;

            // 휠 클릭 패닝 인터랙션 상태
            this.isPanning = false;
            this.panStartX = 0;
            this.panStartY = 0;
            this.startPanX = 0;
            this.startPanY = 0;
            this.tooltipTimer = null;

            this.init();
        }

        init() {
            this.updatePixelDimensions();
            this.bindEvents();
            this.applyTransform();
        }

        updatePixelDimensions() {
            this.cachedViewWidth = window.innerWidth;
            this.cachedViewHeight = window.innerHeight;
            this.cellSize = parseFloat(getComputedStyle(this.gridEl).fontSize) || CONFIG.DEFAULT_CELL_SIZE_PX;
            this.gridPixelWidth = this.gridWidthEm * this.cellSize;
            this.gridPixelHeight = this.gridHeightEm * this.cellSize;
        }

        clampPan(x, y, s = this.scale) {
            const gridWidth = this.gridPixelWidth * s;
            const gridHeight = this.gridPixelHeight * s;
            const viewWidth = this.cachedViewWidth;
            const viewHeight = this.cachedViewHeight;

            let clampedX = x;
            let clampedY = y;

            if (gridWidth > viewWidth) {
                clampedX = Math.min(0, Math.max(viewWidth - gridWidth, x));
            } else {
                clampedX = 0;
            }

            if (gridHeight > viewHeight) {
                clampedY = Math.min(0, Math.max(viewHeight - gridHeight, y));
            } else {
                clampedY = 0;
            }

            return { x: clampedX, y: clampedY };
        }

        applyTransform() {
            this.gridEl.style.transform = `translate(${this.panX}px, ${this.panY}px) scale(${this.scale})`;
        }

        setPan(x, y) {
            const clamped = this.clampPan(x, y);
            this.panX = clamped.x;
            this.panY = clamped.y;
            this.applyTransform();
        }

        zoomAt(newScale, focusX, focusY) {
            const targetScale = Math.min(CONFIG.MAX_SCALE, Math.max(CONFIG.MIN_SCALE, newScale));
            if (targetScale === this.scale) return;

            const canvasX = (focusX - this.panX) / this.scale;
            const canvasY = (focusY - this.panY) / this.scale;

            const targetPanX = focusX - canvasX * targetScale;
            const targetPanY = focusY - canvasY * targetScale;

            this.scale = targetScale;
            const clamped = this.clampPan(targetPanX, targetPanY, targetScale);
            this.panX = clamped.x;
            this.panY = clamped.y;

            this.applyTransform();
            this.showTooltip(focusX + 14, focusY + 14, `${Math.round(this.scale * 200)}%`, CONFIG.TOOLTIP_HIDE_DELAY_MS);
        }

        showTooltip(x, y, text, autoHideDelay = 1000) {
            if (!this.tooltipEl) return;
            this.tooltipEl.textContent = text;

            const tooltipX = Math.min(window.innerWidth - 80, Math.max(10, x));
            const tooltipY = Math.min(window.innerHeight - 40, Math.max(10, y));

            this.tooltipEl.style.transform = `translate(${tooltipX}px, ${tooltipY}px)`;
            this.tooltipEl.classList.add('show');

            if (this.tooltipTimer) clearTimeout(this.tooltipTimer);
            if (autoHideDelay > 0) {
                this.tooltipTimer = setTimeout(() => {
                    this.tooltipEl.classList.remove('show');
                }, autoHideDelay);
            }
        }

        hideTooltip() {
            if (!this.tooltipEl) return;
            this.tooltipEl.classList.remove('show');
            if (this.tooltipTimer) clearTimeout(this.tooltipTimer);
        }

        screenToGrid(clientX, clientY) {
            const canvasX = (clientX - this.panX) / this.scale;
            const canvasY = (clientY - this.panY) / this.scale;
            return {
                x: Math.round(canvasX / this.cellSize),
                y: Math.round(canvasY / this.cellSize)
            };
        }

        screenToGridFloat(clientX, clientY) {
            const canvasX = (clientX - this.panX) / this.scale;
            const canvasY = (clientY - this.panY) / this.scale;
            return {
                x: canvasX / this.cellSize,
                y: canvasY / this.cellSize
            };
        }

        gridToScreen(gridX, gridY) {
            const canvasX = gridX * this.cellSize;
            const canvasY = gridY * this.cellSize;
            return {
                x: canvasX * this.scale + this.panX,
                y: canvasY * this.scale + this.panY
            };
        }

        ensureGridSize(maxColEm, maxRowEm) {
            const targetWidth = Math.max(CONFIG.DEFAULT_GRID_SIZE_EM, Math.ceil(maxColEm) + 2);
            const targetHeight = Math.max(CONFIG.DEFAULT_GRID_SIZE_EM, Math.ceil(maxRowEm) + 2);

            if (targetWidth !== this.gridWidthEm || targetHeight !== this.gridHeightEm) {
                this.gridWidthEm = targetWidth;
                this.gridHeightEm = targetHeight;
                this.gridEl.style.width = `${targetWidth}em`;
                this.gridEl.style.height = `${targetHeight}em`;
                this.updatePixelDimensions();
            }
        }

        bindEvents() {
            // 브라우저 휠 버튼 클릭 시 윈도우 기본 자동 스크롤 모드 방지 (필수)
            window.addEventListener('mousedown', (e) => {
                if (e.button === 1) {
                    e.preventDefault();
                }
            });

            window.addEventListener('resize', () => {
                this.updatePixelDimensions();
                const clamped = this.clampPan(this.panX, this.panY);
                this.panX = clamped.x;
                this.panY = clamped.y;
                this.applyTransform();
            });

            // 마우스 휠: Ctrl + 휠 회전 시 커서 중심 줌 (ZOOM_STEPS 스냅)
            window.addEventListener('wheel', (e) => {
                if (e.ctrlKey) {
                    e.preventDefault();
                    const isZoomIn = e.deltaY < 0;
                    const nextScale = getNextZoomStep(this.scale, isZoomIn);
                    this.zoomAt(nextScale, e.clientX, e.clientY);
                } else if (e.shiftKey) {
                    e.preventDefault();
                    this.setPan(this.panX - e.deltaX, this.panY - e.deltaY);
                }
            }, { passive: false });

            // Ctrl 키 상태에 따른 커서 변경 (zoom-in)
            window.addEventListener('keydown', (e) => {
                if (e.key === 'Control') {
                    document.body.classList.add('is-ctrl-pressed');
                }
            });

            window.addEventListener('keyup', (e) => {
                if (e.key === 'Control') {
                    document.body.classList.remove('is-ctrl-pressed');
                    this.hideTooltip();
                }
            });

            window.addEventListener('blur', () => {
                document.body.classList.remove('is-ctrl-pressed');
                this.hideTooltip();
            });
        }
    }

    // =========================================================================
    // 4. 인메모리 데이터 스토어 & 요소 관리자 (Element Store & Manager)
    // =========================================================================
    class ElementStore {
        constructor(gridEl, viewport) {
            this.gridEl = gridEl;
            this.viewport = viewport;
            this.elementsMap = new Map();
            this.renderQueueTimeout = null;
            this.idleRenderCallbackId = null;
            this.textEditor = null;
        }

        generateId(prefix = 'b') {
            return prefix + Math.random().toString(36).substring(2, 8);
        }

        createBoxPreview(left, top) {
            const boxId = this.generateId('b');
            const boxDiv = document.createElement('div');
            boxDiv.className = 'box';
            boxDiv.id = boxId;
            boxDiv.style.left = `${left}em`;
            boxDiv.style.top = `${top}em`;
            boxDiv.style.width = `1em`;
            boxDiv.style.height = `1em`;
            boxDiv.dataset.left = left;
            boxDiv.dataset.top = top;
            boxDiv.dataset.width = 1;
            boxDiv.dataset.height = 1;

            const contentsDiv = document.createElement('div');
            contentsDiv.className = 'box-contents';

            const textDiv = document.createElement('div');
            textDiv.className = 'box-text';
            contentsDiv.appendChild(textDiv);
            boxDiv.appendChild(contentsDiv);

            // 4방향 에지 리사이즈 핸들
            ['top', 'bottom', 'left', 'right'].forEach(edge => {
                const handle = document.createElement('div');
                handle.className = `box-edge box-edge-${edge}`;
                handle.dataset.edge = edge;
                boxDiv.appendChild(handle);
            });

            this.gridEl.appendChild(boxDiv);
            return boxDiv;
        }

        registerBoxElement(boxDiv, left, top, width, height, text = '', lazy = false) {
            const item = {
                id: boxDiv.id,
                type: 'box',
                left,
                top,
                width,
                height,
                text,
                element: boxDiv,
                isRendered: !lazy
            };

            this.elementsMap.set(boxDiv.id, item);
            this.viewport.ensureGridSize(left + width, top + height);
            if (!lazy) {
                this.renderSingleBox(item);
            }
            return item;
        }

        createBoxElement(id, left, top, width, height, text = '', lazy = false) {
            const boxDiv = this.createBoxPreview(left, top);
            if (id) boxDiv.id = id;
            boxDiv.style.width = `${width}em`;
            boxDiv.style.height = `${height}em`;
            boxDiv.dataset.width = width;
            boxDiv.dataset.height = height;

            const textDiv = boxDiv.querySelector('.box-text');
            if (textDiv) {
                textDiv.innerHTML = lazy ? '' : parseMathToHtml(text);
            }

            this.registerBoxElement(boxDiv, left, top, width, height, text, lazy);
            return boxDiv;
        }

        createLinePreview(left, top) {
            const lineId = this.generateId('l');
            const lineDiv = document.createElement('div');
            lineDiv.className = 'line';
            lineDiv.id = lineId;
            lineDiv.dataset.left = left;
            lineDiv.dataset.top = top;
            lineDiv.dataset.width = 0;
            lineDiv.dataset.height = 0;

            const lineBody = document.createElement('div');
            lineBody.className = 'line-body';
            lineDiv.appendChild(lineBody);

            ['start', 'end'].forEach(point => {
                const handle = document.createElement('div');
                handle.className = `line-point line-point-${point}`;
                handle.dataset.point = point;
                lineDiv.appendChild(handle);
            });

            this.gridEl.appendChild(lineDiv);
            this.updateLineVisual(lineDiv);
            return lineDiv;
        }

        registerLineElement(lineDiv, left, top, width, height) {
            const item = {
                id: lineDiv.id,
                type: 'line',
                left,
                top,
                width,
                height,
                element: lineDiv
            };

            this.elementsMap.set(lineDiv.id, item);
            this.viewport.ensureGridSize(Math.max(left, left + width), Math.max(top, top + height));
            return item;
        }

        createLineElement(id, left, top, width, height) {
            const lineDiv = this.createLinePreview(left, top);
            if (id) lineDiv.id = id;
            lineDiv.dataset.width = width;
            lineDiv.dataset.height = height;
            this.updateLineVisual(lineDiv);

            this.registerLineElement(lineDiv, left, top, width, height);
            return lineDiv;
        }

        updateLineVisual(lineDiv) {
            const left = parseFloat(lineDiv.dataset.left) || 0;
            const top = parseFloat(lineDiv.dataset.top) || 0;
            const width = parseFloat(lineDiv.dataset.width) || 0;
            const height = parseFloat(lineDiv.dataset.height) || 0;

            const length = Math.hypot(width, height);
            const angle = Math.atan2(-width, height);

            lineDiv.style.left = `${left + 0.5}em`;
            lineDiv.style.top = `${top + 0.5}em`;
            lineDiv.style.width = '0';
            lineDiv.style.height = `${length}em`;
            lineDiv.style.transform = `rotate(${angle}rad)`;
        }

        renderSingleBox(item) {
            if (!item || item.type !== 'box') return;
            if (item.isRendered) return;
            const textEl = item.element?.querySelector('.box-text');
            if (!textEl) return;
            if (item.element.classList.contains('is-editing')) return;

            textEl.innerHTML = parseMathToHtml(item.text || '');
            item.isRendered = true;

            if (this.textEditor && typeof this.textEditor.initGraphInContainer === 'function') {
                this.textEditor.initGraphInContainer(textEl);
            }
        }

        renderVisibleBoxes() {
            if (!this.viewport) return;

            // 현재 뷰포트 중심 좌표 (em 단위)
            const windowMidX = window.innerWidth / 2;
            const windowMidY = window.innerHeight / 2;
            const cellSize = this.viewport.cellSize || 32;
            const scale = this.viewport.scale || 1;
            const panX = this.viewport.panX || 0;
            const panY = this.viewport.panY || 0;

            const centerGridX = (windowMidX - panX) / (scale * cellSize);
            const centerGridY = (windowMidY - panY) / (scale * cellSize);

            // 중심 기준 200em x 200em 영역 (반경 100em)
            const rangeHalf = 100;
            const viewMinX = centerGridX - rangeHalf;
            const viewMaxX = centerGridX + rangeHalf;
            const viewMinY = centerGridY - rangeHalf;
            const viewMaxY = centerGridY + rangeHalf;

            const unrenderedOutside = [];

            this.elementsMap.forEach((item) => {
                if (item.type !== 'box') return;
                if (item.isRendered) return;

                const boxRight = item.left + item.width;
                const boxBottom = item.top + item.height;
                const isOverlap = (boxRight >= viewMinX && item.left <= viewMaxX && boxBottom >= viewMinY && item.top <= viewMaxY);

                if (isOverlap) {
                    this.renderSingleBox(item);
                } else {
                    unrenderedOutside.push(item);
                }
            });

            // 200em 영역 밖의 미렌더링 박스들은 브라우저 유휴 시간에 백그라운드 선렌더링
            this.scheduleIdleRendering(unrenderedOutside);
        }

        queueRenderVisibleBoxes(delay = 100) {
            if (this.renderQueueTimeout) clearTimeout(this.renderQueueTimeout);
            this.renderQueueTimeout = setTimeout(() => {
                this.renderVisibleBoxes();
            }, delay);
        }

        scheduleIdleRendering(items) {
            if (!items || items.length === 0) return;
            if (this.idleRenderCallbackId) {
                if ('cancelIdleCallback' in window) {
                    cancelIdleCallback(this.idleRenderCallbackId);
                } else {
                    clearTimeout(this.idleRenderCallbackId);
                }
            }

            const runIdle = (deadline) => {
                let idx = 0;
                while (idx < items.length && (deadline ? deadline.timeRemaining() > 2 : true)) {
                    const item = items[idx++];
                    if (item && !item.isRendered) {
                        this.renderSingleBox(item);
                    }
                }
                if (idx < items.length) {
                    const remaining = items.slice(idx);
                    this.scheduleIdleRendering(remaining);
                }
            };

            if ('requestIdleCallback' in window) {
                this.idleRenderCallbackId = requestIdleCallback(runIdle, { timeout: 2000 });
            } else {
                this.idleRenderCallbackId = setTimeout(() => runIdle(null), 300);
            }
        }

        removeElement(id) {
            const item = this.elementsMap.get(id);
            if (item) {
                if (item.element && item.element.parentNode) {
                    item.element.parentNode.removeChild(item.element);
                }
                this.elementsMap.delete(id);
            }
        }
    }

    // =========================================================================
    // 5. 선택 관리자 (Selection Manager)
    // =========================================================================
    class SelectionManager {
        constructor() {
            this.selectedElements = new Set();
            this.deleteBtn = document.getElementById('delete-btn');
        }

        updateUI() {
            document.querySelectorAll('.box.selected, .line.selected').forEach(el => {
                if (!this.selectedElements.has(el)) {
                    el.classList.remove('selected');
                }
            });

            this.selectedElements.forEach(el => {
                el.classList.add('selected');
            });

            document.body.classList.toggle('single-selected', this.selectedElements.size === 1);
            if (this.deleteBtn) {
                this.deleteBtn.disabled = this.selectedElements.size === 0;
            }
        }

        select(el, isMulti = false) {
            if (!el) {
                this.clear();
                return;
            }
            if (isMulti) {
                if (this.selectedElements.has(el)) {
                    this.selectedElements.delete(el);
                } else {
                    this.selectedElements.add(el);
                }
            } else {
                this.selectedElements.clear();
                this.selectedElements.add(el);
            }
            this.updateUI();
        }

        setSelection(elementsSet) {
            this.selectedElements.clear();
            if (elementsSet) {
                elementsSet.forEach(el => this.selectedElements.add(el));
            }
            this.updateUI();
        }

        clear() {
            this.selectedElements.clear();
            this.updateUI();
        }

        deleteSelected(store, historyManager = this.historyManager) {
            if (this.selectedElements.size === 0) return;
            if (historyManager) {
                historyManager.pushUndoSnapshot(historyManager.captureSnapshot());
            }
            this.selectedElements.forEach(el => {
                store.removeElement(el.id);
            });
            this.clear();
        }
    }

    // =========================================================================
    // 6. 히스토리 관리자 (History Manager - Undo / Redo)
    // =========================================================================
    class HistoryManager {
        constructor(store, viewport, selectionManager, dataManager = null) {
            this.store = store;
            this.viewport = viewport;
            this.selectionManager = selectionManager;
            this.dataManager = dataManager;
            this.undoStack = [];
            this.redoStack = [];
            this.MAX_HISTORY = 50;
            this.snapshotBeforeAction = null;
        }

        captureSnapshot() {
            const list = [];
            this.store.elementsMap.forEach(item => {
                let textContent = '';
                if (item.type === 'box') {
                    if (item.element && item.element.classList.contains('is-editing')) {
                        textContent = item.element.querySelector('.box-text')?.innerHTML || item.text || '';
                    } else {
                        textContent = item.text || '';
                    }
                }
                list.push({
                    id: item.id,
                    type: item.type,
                    left: item.left,
                    top: item.top,
                    width: item.width,
                    height: item.height,
                    text: textContent
                });
            });
            return JSON.stringify(list);
        }

        recordActionStart() {
            this.snapshotBeforeAction = this.captureSnapshot();
        }

        commitAction() {
            if (!this.snapshotBeforeAction) return;
            this.pushUndoSnapshot(this.snapshotBeforeAction);
            this.snapshotBeforeAction = null;
        }

        discardActionStart() {
            this.snapshotBeforeAction = null;
        }

        pushUndoSnapshot(snapshot) {
            if (!snapshot) return;
            const current = this.captureSnapshot();
            if (snapshot === current) return; // 변화가 없으면 기록 안 함

            this.undoStack.push(snapshot);
            if (this.undoStack.length > this.MAX_HISTORY) {
                this.undoStack.shift();
            }
            this.redoStack.length = 0; // 새 액션 시 redo 스택 초기화

            if (this.dataManager) {
                this.dataManager.queueAutoSave();
            }
        }

        restoreSnapshot(jsonStr) {
            if (!jsonStr) return;
            const list = JSON.parse(jsonStr);
            const targetMap = new Map();
            list.forEach(item => targetMap.set(item.id, item));

            // 1. 현재 DOM/elementsMap에 있지만 스냅샷에 없는 요소 삭제
            const currentIds = Array.from(this.store.elementsMap.keys());
            currentIds.forEach(id => {
                if (!targetMap.has(id)) {
                    const data = this.store.elementsMap.get(id);
                    if (data && data.element) {
                        this.selectionManager.selectedElements.delete(data.element);
                    }
                    this.store.removeElement(id);
                }
            });

            // 2. 스냅샷에 있는 요소 복원 및 속성 갱신
            list.forEach(item => {
                let existing = this.store.elementsMap.get(item.id);
                if (!existing) {
                    if (item.type === 'box') {
                        this.store.createBoxElement(item.id, item.left, item.top, item.width, item.height, item.text || '');
                    } else if (item.type === 'line') {
                        this.store.createLineElement(item.id, item.left, item.top, item.width, item.height);
                    }
                } else {
                    existing.left = item.left;
                    existing.top = item.top;
                    existing.width = item.width;
                    existing.height = item.height;
                    existing.text = item.text || '';

                    const el = existing.element;
                    el.dataset.left = item.left;
                    el.dataset.top = item.top;
                    el.dataset.width = item.width;
                    el.dataset.height = item.height;

                    if (item.type === 'box') {
                        el.style.left = `${item.left}em`;
                        el.style.top = `${item.top}em`;
                        el.style.width = `${item.width}em`;
                        el.style.height = `${item.height}em`;
                        const textEl = el.querySelector('.box-text');
                        if (textEl) {
                            textEl.innerHTML = parseMathToHtml(item.text || '');
                        }
                    } else if (item.type === 'line') {
                        this.store.updateLineVisual(el);
                    }
                }
            });

            // 3. 선택 상태 정리
            this.selectionManager.selectedElements.forEach(el => {
                if (!el.isConnected) {
                    this.selectionManager.selectedElements.delete(el);
                }
            });
            this.selectionManager.updateUI();

            // 4. 그리드 크기 갱신
            let maxCol = 0;
            let maxRow = 0;
            this.store.elementsMap.forEach(item => {
                const right = Math.max(item.left, item.left + item.width);
                const bottom = Math.max(item.top, item.top + item.height);
                if (right > maxCol) maxCol = right;
                if (bottom > maxRow) maxRow = bottom;
            });
            this.viewport.ensureGridSize(maxCol, maxRow);
        }

        undo() {
            if (this.undoStack.length === 0) return;
            const current = this.captureSnapshot();
            const prev = this.undoStack.pop();
            this.redoStack.push(current);
            this.restoreSnapshot(prev);

            if (this.dataManager) {
                this.dataManager.queueAutoSave();
            }
        }

        redo() {
            if (this.redoStack.length === 0) return;
            const current = this.captureSnapshot();
            const next = this.redoStack.pop();
            this.undoStack.push(current);
            this.restoreSnapshot(next);

            if (this.dataManager) {
                this.dataManager.queueAutoSave();
            }
        }
    }

    // =========================================================================
    // 7. 텍스트 편집 관리자 (Text Editor Manager)
    // =========================================================================
    class TextEditorManager {
        constructor(store, selectionManager, historyManager = null) {
            this.store = store;
            this.selectionManager = selectionManager;
            this.historyManager = historyManager;
            this.activeBox = null;
            this.textEditingInitialSnapshot = null;

            this.mathBubbleEl = document.getElementById('math-mini-code-bubble');
            this.activeMathTarget = null;
            this.initMathBubbleEvents();

            this.graphBubbleEl = document.getElementById('graph-mini-code-bubble');
            this.activeGraphTarget = null;
            this.initGraphBubbleEvents();

            this.markerBubbleEl = document.getElementById('marker-mini-bubble');
            this.activeMarkerTarget = null;
            this.initMarkerBubbleEvents();
        }

        initMathBubbleEvents() {
            if (!this.mathBubbleEl) return;

            // 버블 내부 클릭 시 캔버스 제스처(이동, 선택 등) 전파 차단
            this.mathBubbleEl.addEventListener('pointerdown', (e) => {
                e.stopPropagation();
            });

            // 수식 입력 중 실시간 렌더링 및 버블 위치 실시간 추적
            this.mathBubbleEl.addEventListener('input', () => {
                if (!this.activeMathTarget) return;
                const code = this.mathBubbleEl.textContent || '';
                this.activeMathTarget.dataset.latex = code;
                this.renderMathTarget(this.activeMathTarget);
                this.positionMathBubble(this.activeMathTarget);
            });

            // 키보드 내비게이션 및 탈출/확정 처리
            this.mathBubbleEl.addEventListener('keydown', (e) => {
                if (!this.activeMathTarget) return;

                // Enter: 수식 확정 및 다음 위치로 탈출
                if (e.key === 'Enter') {
                    if (e.shiftKey) {
                        return; // Shift+Enter: 줄바꿈 허용
                    }
                    e.preventDefault();
                    e.stopPropagation();
                    this.deactivateMathBubble(true, 'next');
                    return;
                }

                // Backspace: 수식이 완전히 비어있을 때 즉시 삭제 및 이전 텍스트로 탈출
                if (e.key === 'Backspace') {
                    const code = this.mathBubbleEl.textContent.trim();
                    if (!code) {
                        e.preventDefault();
                        e.stopPropagation();
                        this.deactivateMathBubble(false, 'prev');
                        return;
                    }
                }

                // ArrowRight / ArrowDown: 버블 텍스트 끝에 있을 때 오른쪽 텍스트로 탈출
                if (e.key === 'ArrowRight' || e.key === 'ArrowDown') {
                    if (this.isCaretAtEnd(this.mathBubbleEl)) {
                        e.preventDefault();
                        e.stopPropagation();
                        this.deactivateMathBubble(true, 'next');
                        return;
                    }
                }

                // ArrowLeft / ArrowUp: 버블 텍스트 맨 앞에 있을 때 왼쪽 텍스트로 탈출
                if (e.key === 'ArrowLeft' || e.key === 'ArrowUp') {
                    if (this.isCaretAtStart(this.mathBubbleEl)) {
                        e.preventDefault();
                        e.stopPropagation();
                        this.deactivateMathBubble(true, 'prev');
                        return;
                    }
                }

                // Escape: 버블 닫기 (비어있으면 자동 삭제)
                if (e.key === 'Escape') {
                    e.preventDefault();
                    e.stopPropagation();
                    this.deactivateMathBubble(true, 'none');
                    return;
                }
            });

            // 순수 텍스트 붙여넣기 (서식 제거)
            this.mathBubbleEl.addEventListener('paste', (e) => {
                e.preventDefault();
                const pasteText = (e.clipboardData || window.clipboardData)?.getData('text/plain') || '';
                if (pasteText) {
                    document.execCommand('insertText', false, pasteText);
                }
            });
        }

        activateMathBubble(mathTarget, cursorPosition = 'end') {
            if (!this.mathBubbleEl || !mathTarget) return;

            if (this.activeMathTarget && this.activeMathTarget !== mathTarget) {
                this.deactivateMathBubble(true, 'none');
            }
            if (this.activeGraphTarget) {
                this.deactivateGraphBubble(true, 'none');
            }

            this.activeMathTarget = mathTarget;

            document.querySelectorAll('.inline-math.is-active').forEach(b => b.classList.remove('is-active'));
            mathTarget.classList.add('is-active');

            this.mathBubbleEl.textContent = mathTarget.dataset.latex || '';
            this.positionMathBubble(mathTarget);
            this.mathBubbleEl.classList.add('show');

            this.focusBlock(this.mathBubbleEl, cursorPosition === 'start');
        }

        positionMathBubble(mathTarget) {
            if (!this.mathBubbleEl || !mathTarget) return;

            const rect = mathTarget.getBoundingClientRect();
            const textLen = (mathTarget.dataset.latex || '').length;
            const bubbleWidth = Math.max(140, Math.min(520, Math.max(textLen * 9 + 40, 160)));

            let left = rect.left + (rect.width / 2) - (bubbleWidth / 2);
            let top = rect.top - 42; // 수식 위쪽

            this.mathBubbleEl.classList.remove('point-down');

            if (top < 10) {
                top = rect.bottom + 8; // 상단 공간 부족 시 아래쪽 표시
                this.mathBubbleEl.classList.add('point-down');
            }

            if (left < 10) left = 10;
            if (left + bubbleWidth > window.innerWidth - 10) {
                left = window.innerWidth - bubbleWidth - 10;
            }

            this.mathBubbleEl.style.left = `${left}px`;
            this.mathBubbleEl.style.top = `${top}px`;
            this.mathBubbleEl.style.minWidth = `${bubbleWidth}px`;
        }

        deactivateMathBubble(save = true, moveCursorDirection = 'none') {
            if (!this.mathBubbleEl) return;

            const target = this.activeMathTarget;
            this.mathBubbleEl.classList.remove('show');

            if (target) {
                target.classList.remove('is-active');
                const rawCode = this.mathBubbleEl.textContent || '';
                const code = rawCode.trim();

                const parent = target.parentNode;
                const nextNode = target.nextSibling;
                const prevNode = target.previousSibling;

                if (save && code) {
                    target.dataset.latex = code;
                    this.renderMathTarget(target);

                    if (moveCursorDirection === 'next') {
                        this.placeCaretAfterNode(target);
                    } else if (moveCursorDirection === 'prev') {
                        this.placeCaretBeforeNode(target);
                    }
                } else {
                    // 수식 코드가 비어있거나 공백만 있다면 자동 삭제 (Self-cleanup)
                    target.remove();

                    if (moveCursorDirection === 'next' && nextNode) {
                        this.placeCaretAtNodeStart(nextNode);
                    } else if (moveCursorDirection === 'prev' && prevNode) {
                        this.placeCaretAtNodeEnd(prevNode);
                    } else if (parent) {
                        this.placeCaretAtEnd(parent);
                    }
                }
            }

            this.activeMathTarget = null;
        }

        renderMathTarget(target) {
            if (!target) return;
            const latex = (target.dataset.latex || '').trim();
            if (!latex) {
                target.innerHTML = `<span style="color: var(--color-e); font-style: italic; font-size: 0.9em; background: color-mix(in srgb, var(--color-c) 50%, transparent); padding: 0 4px; border-radius: 2px;">[$...]</span>`;
                return;
            }

            if (typeof katex !== 'undefined') {
                try {
                    const expr = prepareLatexForRender(latex, false);
                    const rendered = katex.renderToString(expr, {
                        displayMode: false,
                        throwOnError: false,
                        trust: true
                    });
                    target.innerHTML = rendered;
                } catch (err) {
                    target.textContent = `$${latex}$`;
                }
            } else {
                target.textContent = `$${latex}$`;
            }
        }

        createInlineMathElement(latex = '') {
            const span = document.createElement('span');
            span.className = 'inline-math';
            span.dataset.latex = latex || '';
            span.contentEditable = 'false';

            this.renderMathTarget(span);

            span.addEventListener('click', (e) => {
                e.stopPropagation();
                if (this.activeBox && this.activeBox.classList.contains('is-editing')) {
                    this.activateMathBubble(span, 'end');
                }
            });

            return span;
        }

        initMathInContainer(container) {
            if (!container) return;
            container.querySelectorAll('.inline-math').forEach(span => {
                span.contentEditable = 'false';
                this.renderMathTarget(span);

                if (!span._hasMathClickListener) {
                    span._hasMathClickListener = true;
                    span.addEventListener('click', (e) => {
                        e.stopPropagation();
                        if (this.activeBox && this.activeBox.classList.contains('is-editing')) {
                            this.activateMathBubble(span, 'end');
                        }
                    });
                }
            });
        }

        // =========================================================================
        // TikZ 그래프 미니 코드 버블 메서드 (Graph Bubble Methods)
        // =========================================================================
        initGraphBubbleEvents() {
            if (!this.graphBubbleEl) return;

            // 버블 내부 클릭 시 캔버스 제스처(이동, 선택 등) 전파 차단
            this.graphBubbleEl.addEventListener('pointerdown', (e) => {
                e.stopPropagation();
            });

            // 실시간 렌더링 및 버블 위치 실시간 추적
            this.graphBubbleEl.addEventListener('input', () => {
                if (!this.activeGraphTarget) return;
                const code = this.graphBubbleEl.textContent || '';
                this.activeGraphTarget.dataset.tikz = code;
                this.renderGraphTarget(this.activeGraphTarget);
                this.positionGraphBubble(this.activeGraphTarget);
            });

            // 키보드 내비게이션 및 탈출/확정 처리
            this.graphBubbleEl.addEventListener('keydown', (e) => {
                if (!this.activeGraphTarget) return;

                // Enter (Shift 없는 경우): 확정 및 다음 위치로 탈출
                if (e.key === 'Enter') {
                    if (e.shiftKey) {
                        return; // Shift+Enter: 줄바꿈 허용
                    }
                    e.preventDefault();
                    e.stopPropagation();
                    this.deactivateGraphBubble(true, 'next');
                    return;
                }

                // Backspace: 코드가 비어있을 때 즉시 삭제 및 이전 텍스트로 탈출
                if (e.key === 'Backspace') {
                    const code = this.graphBubbleEl.textContent.trim();
                    if (!code) {
                        e.preventDefault();
                        e.stopPropagation();
                        this.deactivateGraphBubble(false, 'prev');
                        return;
                    }
                }

                // ArrowRight / ArrowDown: 버블 텍스트 끝에 있을 때 오른쪽 텍스트로 탈출
                if (e.key === 'ArrowRight' || e.key === 'ArrowDown') {
                    if (this.isCaretAtEnd(this.graphBubbleEl)) {
                        e.preventDefault();
                        e.stopPropagation();
                        this.deactivateGraphBubble(true, 'next');
                        return;
                    }
                }

                // ArrowLeft / ArrowUp: 버블 텍스트 맨 앞에 있을 때 왼쪽 텍스트로 탈출
                if (e.key === 'ArrowLeft' || e.key === 'ArrowUp') {
                    if (this.isCaretAtStart(this.graphBubbleEl)) {
                        e.preventDefault();
                        e.stopPropagation();
                        this.deactivateGraphBubble(true, 'prev');
                        return;
                    }
                }

                // Escape: 버블 닫기 (비어있으면 자동 삭제)
                if (e.key === 'Escape') {
                    e.preventDefault();
                    e.stopPropagation();
                    this.deactivateGraphBubble(true, 'none');
                    return;
                }
            });

            // 순수 텍스트 붙여넣기
            this.graphBubbleEl.addEventListener('paste', (e) => {
                e.preventDefault();
                const pasteText = (e.clipboardData || window.clipboardData)?.getData('text/plain') || '';
                if (pasteText) {
                    document.execCommand('insertText', false, pasteText);
                }
            });
        }

        activateGraphBubble(graphTarget, cursorPosition = 'end') {
            if (!this.graphBubbleEl || !graphTarget) return;

            if (this.activeGraphTarget && this.activeGraphTarget !== graphTarget) {
                this.deactivateGraphBubble(true, 'none');
            }
            if (this.activeMathTarget) {
                this.deactivateMathBubble(true, 'none');
            }
            if (this.activeMarkerTarget) {
                this.deactivateMarkerBubble(true);
            }

            this.activeGraphTarget = graphTarget;

            document.querySelectorAll('.inline-graph.is-active').forEach(b => b.classList.remove('is-active'));
            graphTarget.classList.add('is-active');

            this.graphBubbleEl.textContent = graphTarget.dataset.tikz || '';
            this.positionGraphBubble(graphTarget);
            this.graphBubbleEl.classList.add('show');

            this.focusBlock(this.graphBubbleEl, cursorPosition === 'start');
        }

        positionGraphBubble(graphTarget) {
            if (!this.graphBubbleEl || !graphTarget) return;

            const rect = graphTarget.getBoundingClientRect();
            const textLen = (graphTarget.dataset.tikz || '').length;
            const bubbleWidth = Math.max(220, Math.min(580, Math.max(textLen * 8 + 60, 240)));

            let left = rect.left + (rect.width / 2) - (bubbleWidth / 2);
            let top = rect.top - 46; // 그래프 위쪽

            this.graphBubbleEl.classList.remove('point-down');

            if (top < 10) {
                top = rect.bottom + 8; // 상단 공간 부족 시 아래쪽 표시
                this.graphBubbleEl.classList.add('point-down');
            }

            if (left < 10) left = 10;
            if (left + bubbleWidth > window.innerWidth - 10) {
                left = window.innerWidth - bubbleWidth - 10;
            }

            this.graphBubbleEl.style.left = `${left}px`;
            this.graphBubbleEl.style.top = `${top}px`;
            this.graphBubbleEl.style.minWidth = `${bubbleWidth}px`;
        }

        deactivateGraphBubble(save = true, moveCursorDirection = 'none') {
            if (!this.graphBubbleEl) return;

            const target = this.activeGraphTarget;
            this.graphBubbleEl.classList.remove('show');

            if (target) {
                target.classList.remove('is-active');
                const rawCode = this.graphBubbleEl.textContent || '';
                const code = rawCode.trim();

                const parent = target.parentNode;
                const nextNode = target.nextSibling;
                const prevNode = target.previousSibling;

                if (save && code) {
                    target.dataset.tikz = code;
                    this.renderGraphTarget(target);

                    if (moveCursorDirection === 'next') {
                        this.placeCaretAfterNode(target);
                    } else if (moveCursorDirection === 'prev') {
                        this.placeCaretBeforeNode(target);
                    }
                } else {
                    target.remove();

                    if (moveCursorDirection === 'next' && nextNode) {
                        this.placeCaretAtNodeStart(nextNode);
                    } else if (moveCursorDirection === 'prev' && prevNode) {
                        this.placeCaretAtNodeEnd(prevNode);
                    } else if (parent) {
                        this.placeCaretAtEnd(parent);
                    }
                }
            }

            this.activeGraphTarget = null;
        }

        renderGraphTarget(target) {
            if (!target) return;
            const tikz = (target.dataset.tikz || '').trim();
            if (!tikz) {
                target.innerHTML = `<span class="graph-empty-placeholder">[그래프...]</span>`;
                return;
            }

            try {
                const svgHtml = renderTikzToHtml(tikz);
                if (svgHtml) {
                    target.innerHTML = svgHtml.trim();
                } else {
                    target.innerHTML = `<span class="graph-empty-placeholder">[그래프...]</span>`;
                }
            } catch (err) {
                console.error('TikZ render error:', err);
                target.innerHTML = `<span style="color: #f85149; font-size: 0.85em; background: rgba(248,81,73,0.1); padding: 2px 4px; border-radius: 2px;">그래프 오류</span>`;
            }
        }

        createInlineGraphElement(tikz = '') {
            const span = document.createElement('span');
            span.className = 'inline-graph';
            span.dataset.tikz = tikz || '';
            span.contentEditable = 'false';

            this.renderGraphTarget(span);

            span.addEventListener('click', (e) => {
                e.stopPropagation();
                if (this.activeBox && this.activeBox.classList.contains('is-editing')) {
                    this.activateGraphBubble(span, 'end');
                }
            });

            return span;
        }

        initGraphInContainer(container) {
            if (!container) return;
            container.querySelectorAll('.inline-graph').forEach(span => {
                span.contentEditable = 'false';
                this.renderGraphTarget(span);

                if (!span._hasGraphClickListener) {
                    span._hasGraphClickListener = true;
                    span.addEventListener('click', (e) => {
                        e.stopPropagation();
                        if (this.activeBox && this.activeBox.classList.contains('is-editing')) {
                            this.activateGraphBubble(span, 'end');
                        }
                    });
                }
            });
        }

        insertNewGraphAtCaret() {
            if (!this.activeBox) return;
            const textEl = this.activeBox.querySelector('.box-text');
            if (!textEl) return;

            textEl.focus();

            const sel = window.getSelection();
            let range = null;
            if (sel && sel.rangeCount > 0) {
                const r = sel.getRangeAt(0);
                if (textEl.contains(r.commonAncestorContainer)) {
                    range = r;
                }
            }

            if (!range && this.savedSelectionRange) {
                range = this.savedSelectionRange;
            }

            if (!range) {
                this.placeCaretAtEnd(textEl);
                const s = window.getSelection();
                if (s && s.rangeCount > 0) range = s.getRangeAt(0);
            }

            if (!range) return;

            range.deleteContents();

            const graphSpan = this.createInlineGraphElement('');
            range.insertNode(graphSpan);

            // 바로 뒤에 텍스트 노드가 없으면 빈 텍스트 노드 추가하여 커서 탈출 지원
            if (!graphSpan.nextSibling) {
                graphSpan.parentNode.appendChild(document.createTextNode(''));
            }

            this.activateGraphBubble(graphSpan, 'end');
        }


        getNextSiblingInlineGraph() {
            const sel = window.getSelection();
            if (!sel || !sel.rangeCount) return null;
            const range = sel.getRangeAt(0);
            if (!range.collapsed) return null;

            let node = range.endContainer;
            let offset = range.endOffset;

            if (node.nodeType === Node.TEXT_NODE) {
                if (offset === node.length) {
                    let next = node.nextSibling;
                    while (next && next.nodeType === Node.TEXT_NODE && next.length === 0) {
                        next = next.nextSibling;
                    }
                    if (next && next.classList && next.classList.contains('inline-graph')) {
                        return next;
                    }
                }
            } else if (node.nodeType === Node.ELEMENT_NODE) {
                const child = node.childNodes[offset];
                if (child && child.classList && child.classList.contains('inline-graph')) {
                    return child;
                }
            }
            return null;
        }

        getPrevSiblingInlineGraph() {
            const sel = window.getSelection();
            if (!sel || !sel.rangeCount) return null;
            const range = sel.getRangeAt(0);
            if (!range.collapsed) return null;

            let node = range.startContainer;
            let offset = range.startOffset;

            if (node.nodeType === Node.TEXT_NODE) {
                if (offset === 0) {
                    let prev = node.previousSibling;
                    while (prev && prev.nodeType === Node.TEXT_NODE && prev.length === 0) {
                        prev = prev.previousSibling;
                    }
                    if (prev && prev.classList && prev.classList.contains('inline-graph')) {
                        return prev;
                    }
                }
            } else if (node.nodeType === Node.ELEMENT_NODE) {
                const child = node.childNodes[offset - 1];
                if (child && child.classList && child.classList.contains('inline-graph')) {
                    return child;
                }
            }
            return null;
        }

        initMarkerBubbleEvents() {
            if (!this.markerBubbleEl) return;

            // 버블 내부 클릭 시 캔버스 제스처(이동, 선택 등) 전파 차단
            this.markerBubbleEl.addEventListener('pointerdown', (e) => {
                e.stopPropagation();
            });

            // 기호 입력 중 버블 위치 및 크기 실시간 업데이트
            this.markerBubbleEl.addEventListener('input', () => {
                if (!this.activeMarkerTarget) return;
                this.positionMarkerBubble(this.activeMarkerTarget);
            });

            // 키보드 내비게이션 및 탈출/확정 처리
            this.markerBubbleEl.addEventListener('keydown', (e) => {
                if (!this.activeMarkerTarget) return;

                // Enter: 기호 확정 및 내용 영역으로 포커스
                if (e.key === 'Enter') {
                    e.preventDefault();
                    e.stopPropagation();
                    this.deactivateMarkerBubble(true);
                    return;
                }

                // Escape: 취소하고 버블 닫기
                if (e.key === 'Escape') {
                    e.preventDefault();
                    e.stopPropagation();
                    this.deactivateMarkerBubble(false);
                    return;
                }
            });

            // 순수 텍스트 붙여넣기
            this.markerBubbleEl.addEventListener('paste', (e) => {
                e.preventDefault();
                const pasteText = (e.clipboardData || window.clipboardData)?.getData('text/plain') || '';
                if (pasteText) {
                    document.execCommand('insertText', false, pasteText.trim());
                }
            });
        }

        activateMarkerBubble(markerEl) {
            if (!this.markerBubbleEl || !markerEl) return;

            if (this.activeMarkerTarget && this.activeMarkerTarget !== markerEl) {
                this.deactivateMarkerBubble(true);
            }

            if (this.activeMathTarget) {
                this.deactivateMathBubble(true, 'none');
            }
            if (this.activeGraphTarget) {
                this.deactivateGraphBubble(true, 'none');
            }

            this.activeMarkerTarget = markerEl;

            document.querySelectorAll('.bullet-marker.is-active').forEach(b => b.classList.remove('is-active'));
            markerEl.classList.add('is-active');

            this.markerBubbleEl.textContent = markerEl.textContent || '•';
            this.positionMarkerBubble(markerEl);
            this.markerBubbleEl.classList.add('show');

            this.focusBlock(this.markerBubbleEl, false);
            try {
                const range = document.createRange();
                range.selectNodeContents(this.markerBubbleEl);
                const sel = window.getSelection();
                sel?.removeAllRanges();
                sel?.addRange(range);
            } catch (_) {}
        }

        positionMarkerBubble(markerEl) {
            if (!this.markerBubbleEl || !markerEl) return;

            const rect = markerEl.getBoundingClientRect();
            const textLen = (this.markerBubbleEl.textContent || '').length;
            const bubbleWidth = Math.max(70, Math.min(200, textLen * 11 + 36));

            let left = rect.left + (rect.width / 2) - (bubbleWidth / 2);
            let top = rect.top - 42; // 마커 위쪽

            this.markerBubbleEl.classList.remove('point-down');

            if (top < 10) {
                top = rect.bottom + 8; // 상단 공간 부족 시 아래쪽 표시
                this.markerBubbleEl.classList.add('point-down');
            }

            if (left < 10) left = 10;
            if (left + bubbleWidth > window.innerWidth - 10) {
                left = window.innerWidth - bubbleWidth - 10;
            }

            this.markerBubbleEl.style.left = `${left}px`;
            this.markerBubbleEl.style.top = `${top}px`;
            this.markerBubbleEl.style.minWidth = `${bubbleWidth}px`;
        }

        deactivateMarkerBubble(save = true) {
            if (!this.markerBubbleEl) return;

            const target = this.activeMarkerTarget;
            this.markerBubbleEl.classList.remove('show');

            if (target) {
                target.classList.remove('is-active');
                if (save) {
                    const rawVal = this.markerBubbleEl.textContent || '';
                    const val = rawVal.trim();
                    target.textContent = val || '•';
                }

                // 해당 글머리 기호의 내용 영역으로 포커스 복원
                const bulletItem = target.closest('.bullet-item');
                const contentEl = bulletItem?.querySelector('.bullet-content');
                if (contentEl) {
                    this.focusBlock(contentEl, true);
                }
            }

            this.activeMarkerTarget = null;
        }

        createBulletItemElement(marker = '•', contentHtml = '<br>') {
            const item = document.createElement('div');
            item.className = 'bullet-item';

            const markerEl = document.createElement('span');
            markerEl.className = 'bullet-marker';
            markerEl.contentEditable = 'false';
            markerEl.textContent = marker || '•';

            markerEl.addEventListener('click', (e) => {
                e.stopPropagation();
                if (this.activeBox && this.activeBox.classList.contains('is-editing')) {
                    this.activateMarkerBubble(markerEl);
                }
            });

            const contentEl = document.createElement('div');
            contentEl.className = 'bullet-content';
            contentEl.innerHTML = contentHtml || '<br>';

            item.appendChild(markerEl);
            item.appendChild(contentEl);

            return item;
        }

        initBulletsInContainer(container) {
            if (!container) return;
            container.querySelectorAll('.bullet-marker').forEach(markerEl => {
                markerEl.contentEditable = 'false';
                if (!markerEl._hasMarkerClickListener) {
                    markerEl._hasMarkerClickListener = true;
                    markerEl.addEventListener('click', (e) => {
                        e.stopPropagation();
                        if (this.activeBox && this.activeBox.classList.contains('is-editing')) {
                            this.activateMarkerBubble(markerEl);
                        }
                    });
                }
            });
        }

        getCurrentBulletItem() {
            const sel = window.getSelection();
            if (!sel || !sel.rangeCount) return null;
            const range = sel.getRangeAt(0);
            let node = range.startContainer;
            if (node.nodeType === Node.TEXT_NODE) {
                node = node.parentNode;
            }
            const item = node?.closest?.('.bullet-item');
            if (item && this.activeBox && this.activeBox.contains(item)) {
                return item;
            }
            return null;
        }

        insertBulletItem() {
            if (!this.activeBox) return;
            const textEl = this.activeBox.querySelector('.box-text');
            if (!textEl) return;

            textEl.focus();

            const sel = window.getSelection();
            let range = null;
            if (sel && sel.rangeCount > 0) {
                const r = sel.getRangeAt(0);
                if (textEl.contains(r.commonAncestorContainer)) {
                    range = r;
                }
            }
            if (!range && this.savedSelectionRange) {
                range = this.savedSelectionRange;
            }

            const newBullet = this.createBulletItemElement('•', '<br>');
            const contentEl = newBullet.querySelector('.bullet-content');

            if (!range) {
                textEl.appendChild(newBullet);
            } else {
                let targetBlock = range.startContainer;
                while (targetBlock && targetBlock.parentNode !== textEl) {
                    targetBlock = targetBlock.parentNode;
                }

                if (targetBlock) {
                    if (targetBlock.style.paddingLeft) {
                        newBullet.style.paddingLeft = targetBlock.style.paddingLeft;
                    }
                    if (targetBlock.classList && targetBlock.classList.contains('bullet-item')) {
                        targetBlock.after(newBullet);
                    } else if (targetBlock.tagName === 'P') {
                        // 만약 현재 p가 비어있다면 p를 bullet-item으로 교체
                        const isEmpty = (!targetBlock.textContent || targetBlock.textContent === '') && !targetBlock.querySelector('.inline-math, .inline-graph');
                        if (isEmpty) {
                            targetBlock.replaceWith(newBullet);
                        } else {
                            targetBlock.after(newBullet);
                        }
                    } else {
                        targetBlock.after(newBullet);
                    }
                } else {
                    textEl.appendChild(newBullet);
                }
            }

            this.focusBlock(contentEl, true);
        }

        handleBulletEnter(currentBullet) {
            const contentEl = currentBullet.querySelector('.bullet-content');
            if (!contentEl) return;

            // 내용이 비어있는 글머리 기호에서 엔터를 누르면 일반 문단(<p><br></p>)으로 전환
            const isEmpty = (!contentEl.textContent || contentEl.textContent.trim() === '') && !contentEl.querySelector('.inline-math, .inline-graph');
            if (isEmpty) {
                this.removeBulletItem(currentBullet);
                return;
            }

            const sel = window.getSelection();
            const newBullet = this.createBulletItemElement('•', '<br>');
            if (currentBullet.style.paddingLeft) {
                newBullet.style.paddingLeft = currentBullet.style.paddingLeft;
            }
            const newContent = newBullet.querySelector('.bullet-content');

            if (!sel || !sel.rangeCount) {
                currentBullet.after(newBullet);
                this.focusBlock(newContent, true);
                return;
            }

            const range = sel.getRangeAt(0);

            if (contentEl.contains(range.startContainer)) {
                const splitRange = range.cloneRange();
                splitRange.setEnd(contentEl, contentEl.childNodes.length);
                const extractedFrag = splitRange.extractContents();

                if (extractedFrag && (extractedFrag.textContent !== '' || (extractedFrag.querySelector && extractedFrag.querySelector('.inline-math, .inline-graph')))) {
                    newContent.innerHTML = '';
                    newContent.appendChild(extractedFrag);
                } else {
                    newContent.innerHTML = '<br>';
                }

                if (!contentEl.childNodes.length || contentEl.innerHTML.trim() === '') {
                    contentEl.innerHTML = '<br>';
                }
            } else {
                newContent.innerHTML = '<br>';
            }

            currentBullet.after(newBullet);
            this.focusBlock(newContent, true);
        }

        removeBulletItem(currentBullet) {
            const contentEl = currentBullet.querySelector('.bullet-content');
            const textEl = this.activeBox?.querySelector('.box-text');
            if (!textEl || !contentEl) return;

            const p = document.createElement('p');
            if (currentBullet.style.paddingLeft) {
                p.style.paddingLeft = currentBullet.style.paddingLeft;
            }

            while (contentEl.firstChild) {
                p.appendChild(contentEl.firstChild);
            }

            if (!p.childNodes.length || (p.textContent === '' && !p.querySelector('.inline-math, .inline-graph'))) {
                p.innerHTML = '<br>';
            }

            currentBullet.replaceWith(p);
            this.focusBlock(p, true);
        }

        applyFormat(formatType) {
            if (!this.activeBox) return;
            const textEl = this.activeBox.querySelector('.box-text');
            if (!textEl) return;

            textEl.focus();

            const sel = window.getSelection();
            if (this.savedSelectionRange && (!sel || sel.rangeCount === 0 || !textEl.contains(sel.anchorNode))) {
                sel.removeAllRanges();
                sel.addRange(this.savedSelectionRange);
            }

            try {
                document.execCommand('styleWithCSS', false, false);
            } catch (_) {}

            if (formatType === 'bold') {
                document.execCommand('bold', false, null);
            } else if (formatType === 'italic') {
                document.execCommand('italic', false, null);
            } else if (formatType === 'underline') {
                document.execCommand('underline', false, null);
            }

            const currentSel = window.getSelection();
            if (currentSel && currentSel.rangeCount > 0 && textEl.contains(currentSel.anchorNode)) {
                this.savedSelectionRange = currentSel.getRangeAt(0).cloneRange();
            }
        }

        applyAlignment(alignType) {
            if (!this.activeBox) return;
            const textEl = this.activeBox.querySelector('.box-text');
            if (!textEl) return;

            textEl.focus();

            const sel = window.getSelection();
            if (this.savedSelectionRange && (!sel || sel.rangeCount === 0 || !textEl.contains(sel.anchorNode))) {
                sel.removeAllRanges();
                sel.addRange(this.savedSelectionRange);
            }

            const currentSel = window.getSelection();
            if (!currentSel || currentSel.rangeCount === 0) return;
            const range = currentSel.getRangeAt(0);
            if (!textEl.contains(range.commonAncestorContainer)) return;

            // 모든 문단/블록 요소(<p>, .bullet-item, div) 수집
            const allBlocks = Array.from(textEl.children).filter(el => 
                el.tagName === 'P' || el.classList.contains('bullet-item') || el.tagName === 'DIV'
            );

            const targetBlocks = allBlocks.filter(block => {
                if (range.collapsed) {
                    return block === range.startContainer || block.contains(range.startContainer);
                } else {
                    return range.intersectsNode(block);
                }
            });

            if (targetBlocks.length === 0 && allBlocks.length > 0) {
                targetBlocks.push(allBlocks[0]);
            }

            targetBlocks.forEach(block => {
                const target = block.classList.contains('bullet-item') ? block.querySelector('.bullet-content') : block;
                if (!target) return;

                if (alignType === 'left') {
                    target.style.textAlign = '';
                    if (!target.getAttribute('style') || target.style.cssText.trim() === '') {
                        target.removeAttribute('style');
                    }
                } else {
                    target.style.textAlign = alignType;
                }
            });

            if (currentSel.rangeCount > 0) {
                this.savedSelectionRange = currentSel.getRangeAt(0).cloneRange();
            }
        }

        getBlockIndent(block) {
            if (!block || !block.style) return 0;
            const pad = block.style.paddingLeft || '';
            if (!pad) return 0;
            const match = pad.match(/^([\d.]+)\s*em$/i);
            if (match) {
                return parseFloat(match[1]) || 0;
            }
            const num = parseFloat(pad);
            if (isNaN(num)) return 0;
            if (pad.endsWith('px')) {
                return Math.round(num / 16);
            }
            return Math.round(num);
        }

        applyIndent(delta) {
            if (!this.activeBox) return;
            const textEl = this.activeBox.querySelector('.box-text');
            if (!textEl) return;

            textEl.focus();

            const sel = window.getSelection();
            if (this.savedSelectionRange && (!sel || sel.rangeCount === 0 || !textEl.contains(sel.anchorNode))) {
                sel.removeAllRanges();
                sel.addRange(this.savedSelectionRange);
            }

            const currentSel = window.getSelection();
            if (!currentSel || currentSel.rangeCount === 0) return;
            const range = currentSel.getRangeAt(0);
            if (!textEl.contains(range.commonAncestorContainer)) return;

            // 모든 문단/블록 요소(<p>, .bullet-item, div) 수집
            const allBlocks = Array.from(textEl.children).filter(el => 
                el.tagName === 'P' || el.classList.contains('bullet-item') || el.tagName === 'DIV'
            );

            const targetBlocks = allBlocks.filter(block => {
                if (range.collapsed) {
                    return block === range.startContainer || block.contains(range.startContainer);
                } else {
                    return range.intersectsNode(block);
                }
            });

            if (targetBlocks.length === 0 && allBlocks.length > 0) {
                const cur = this.getCurrentBlock(textEl);
                if (cur) targetBlocks.push(cur);
                else targetBlocks.push(allBlocks[0]);
            }

            targetBlocks.forEach(block => {
                const curPadding = this.getBlockIndent(block);
                const nextPadding = Math.max(0, Math.min(10, Math.round(curPadding + delta)));

                if (nextPadding > 0) {
                    block.style.paddingLeft = `${nextPadding}em`;
                } else {
                    block.style.paddingLeft = '';
                    if (!block.getAttribute('style') || block.style.cssText.trim() === '') {
                        block.removeAttribute('style');
                    }
                }
            });

            if (currentSel.rangeCount > 0) {
                this.savedSelectionRange = currentSel.getRangeAt(0).cloneRange();
            }
        }

        getBlockMarginBottom(block) {
            if (!block || !block.style) return 0;
            const mb = block.style.marginBottom || '';
            if (!mb) return 0;
            const match = mb.match(/^([+-]?[\d.]+)\s*em$/i);
            if (match) {
                return parseFloat(match[1]) || 0;
            }
            const num = parseFloat(mb);
            if (isNaN(num)) return 0;
            if (mb.endsWith('px')) {
                return Math.round((num / 16) * 100) / 100;
            }
            return num;
        }

        showMarginTooltip(targetEl, marginVal) {
            let tip = document.getElementById('margin-feedback-tooltip');
            if (!tip) {
                tip = document.createElement('div');
                tip.id = 'margin-feedback-tooltip';
                tip.className = 'margin-feedback-tooltip';
                document.body.appendChild(tip);
            }

            if (this._marginTipTimer) {
                clearTimeout(this._marginTipTimer);
                this._marginTipTimer = null;
            }

            let text = '';
            if (marginVal > 0) {
                text = `아래 여백: +${marginVal.toFixed(2)}em`;
            } else if (marginVal < 0) {
                text = `아래 여백: ${marginVal.toFixed(2)}em`;
            } else {
                text = '아래 여백: 0em (기본)';
            }
            tip.textContent = text;

            if (targetEl && targetEl.getBoundingClientRect) {
                const rect = targetEl.getBoundingClientRect();
                const tipWidth = 140;
                let left = rect.left + 8;
                let top = rect.bottom + 6;

                // 화면 벗어남 방지 보정
                if (left + tipWidth > window.innerWidth - 10) {
                    left = window.innerWidth - tipWidth - 10;
                }
                if (left < 10) left = 10;

                if (top + 32 > window.innerHeight - 10) {
                    top = rect.top - 34;
                }

                tip.style.left = `${left}px`;
                tip.style.top = `${top}px`;
            }

            tip.classList.add('show');

            this._marginTipTimer = setTimeout(() => {
                tip.classList.remove('show');
            }, 1200);
        }

        applyBottomMargin(delta) {
            if (!this.activeBox) return;
            const textEl = this.activeBox.querySelector('.box-text');
            if (!textEl) return;

            textEl.focus();

            const sel = window.getSelection();
            if (this.savedSelectionRange && (!sel || sel.rangeCount === 0 || !textEl.contains(sel.anchorNode))) {
                sel.removeAllRanges();
                sel.addRange(this.savedSelectionRange);
            }

            const currentSel = window.getSelection();
            if (!currentSel || currentSel.rangeCount === 0) return;
            const range = currentSel.getRangeAt(0);
            if (!textEl.contains(range.commonAncestorContainer)) return;

            // 모든 문단/블록 요소(<p>, .bullet-item, div) 수집
            const allBlocks = Array.from(textEl.children).filter(el => 
                el.tagName === 'P' || el.classList.contains('bullet-item') || el.tagName === 'DIV'
            );

            const targetBlocks = allBlocks.filter(block => {
                if (range.collapsed) {
                    return block === range.startContainer || block.contains(range.startContainer);
                } else {
                    return range.intersectsNode(block);
                }
            });

            if (targetBlocks.length === 0 && allBlocks.length > 0) {
                const cur = this.getCurrentBlock(textEl);
                if (cur) targetBlocks.push(cur);
                else targetBlocks.push(allBlocks[0]);
            }

            let lastVal = 0;
            targetBlocks.forEach(block => {
                const curMargin = this.getBlockMarginBottom(block);
                // 최솟값 -2.0em, 최댓값 +2.0em, 0.25em 단위 증감
                const nextMargin = Math.max(-2, Math.min(2, Math.round((curMargin + delta) * 100) / 100));
                lastVal = nextMargin;

                if (nextMargin !== 0) {
                    block.style.marginBottom = `${nextMargin}em`;
                } else {
                    block.style.marginBottom = '';
                    if (!block.getAttribute('style') || block.style.cssText.trim() === '') {
                        block.removeAttribute('style');
                    }
                }
            });

            if (targetBlocks.length > 0) {
                this.showMarginTooltip(targetBlocks[targetBlocks.length - 1], lastVal);
            }

            if (currentSel.rangeCount > 0) {
                this.savedSelectionRange = currentSel.getRangeAt(0).cloneRange();
            }
        }

        insertNewMathAtCaret() {
            if (!this.activeBox) return;
            const textEl = this.activeBox.querySelector('.box-text');
            if (!textEl) return;

            textEl.focus();

            const sel = window.getSelection();
            let range = null;
            if (sel && sel.rangeCount > 0) {
                const r = sel.getRangeAt(0);
                if (textEl.contains(r.commonAncestorContainer)) {
                    range = r;
                }
            }

            if (!range && this.savedSelectionRange) {
                range = this.savedSelectionRange;
            }

            if (!range) {
                this.placeCaretAtEnd(textEl);
                const s = window.getSelection();
                if (s && s.rangeCount > 0) range = s.getRangeAt(0);
            }

            if (!range) return;

            const selectedText = range.toString().trim();
            range.deleteContents();

            const mathSpan = this.createInlineMathElement(selectedText);
            range.insertNode(mathSpan);

            // 바로 뒤에 텍스트 노드가 없으면 빈 텍스트 노드 추가하여 커서 탈출 지원
            if (!mathSpan.nextSibling) {
                mathSpan.parentNode.appendChild(document.createTextNode(''));
            }

            this.activateMathBubble(mathSpan, 'end');
        }

        getNextSiblingInlineMath() {
            const sel = window.getSelection();
            if (!sel || !sel.rangeCount) return null;
            const range = sel.getRangeAt(0);
            if (!range.collapsed) return null;

            let node = range.endContainer;
            let offset = range.endOffset;

            if (node.nodeType === Node.TEXT_NODE) {
                if (offset === node.length) {
                    let next = node.nextSibling;
                    while (next && next.nodeType === Node.TEXT_NODE && next.length === 0) {
                        next = next.nextSibling;
                    }
                    if (next && next.classList && next.classList.contains('inline-math')) {
                        return next;
                    }
                }
            } else if (node.nodeType === Node.ELEMENT_NODE) {
                const child = node.childNodes[offset];
                if (child && child.classList && child.classList.contains('inline-math')) {
                    return child;
                }
            }
            return null;
        }

        getPrevSiblingInlineMath() {
            const sel = window.getSelection();
            if (!sel || !sel.rangeCount) return null;
            const range = sel.getRangeAt(0);
            if (!range.collapsed) return null;

            let node = range.startContainer;
            let offset = range.startOffset;

            if (node.nodeType === Node.TEXT_NODE) {
                if (offset === 0) {
                    let prev = node.previousSibling;
                    while (prev && prev.nodeType === Node.TEXT_NODE && prev.length === 0) {
                        prev = prev.previousSibling;
                    }
                    if (prev && prev.classList && prev.classList.contains('inline-math')) {
                        return prev;
                    }
                }
            } else if (node.nodeType === Node.ELEMENT_NODE) {
                const child = node.childNodes[offset - 1];
                if (child && child.classList && child.classList.contains('inline-math')) {
                    return child;
                }
            }
            return null;
        }

        isCaretAtStart(el) {
            const sel = window.getSelection();
            if (!sel || !sel.rangeCount) return false;
            const range = sel.getRangeAt(0);
            if (!range.collapsed) return false;

            const testRange = range.cloneRange();
            testRange.selectNodeContents(el);
            testRange.setEnd(range.startContainer, range.startOffset);
            return testRange.toString().length === 0;
        }

        isCaretAtEnd(el) {
            const sel = window.getSelection();
            if (!sel || !sel.rangeCount) return false;
            const range = sel.getRangeAt(0);
            if (!range.collapsed) return false;

            const testRange = range.cloneRange();
            testRange.selectNodeContents(el);
            testRange.setStart(range.endContainer, range.endOffset);
            return testRange.toString().length === 0;
        }

        focusBlock(el, atStart = true) {
            if (!el) return;
            el.focus();
            try {
                const range = document.createRange();
                range.selectNodeContents(el);
                range.collapse(atStart);
                const sel = window.getSelection();
                if (sel) {
                    sel.removeAllRanges();
                    sel.addRange(range);
                }
            } catch (_) {}
        }

        placeCaretAtNodeStart(node) {
            if (!node) return;
            const range = document.createRange();
            if (node.nodeType === Node.TEXT_NODE) {
                range.setStart(node, 0);
            } else {
                range.selectNodeContents(node);
            }
            range.collapse(true);
            const sel = window.getSelection();
            sel?.removeAllRanges();
            sel?.addRange(range);
        }

        placeCaretAtNodeEnd(node) {
            if (!node) return;
            const range = document.createRange();
            if (node.nodeType === Node.TEXT_NODE) {
                range.setStart(node, node.length);
            } else {
                range.selectNodeContents(node);
            }
            range.collapse(false);
            const sel = window.getSelection();
            sel?.removeAllRanges();
            sel?.addRange(range);
        }

        placeCaretAfterNode(node) {
            if (!node || !node.parentNode) return;
            const parent = node.parentNode;
            let targetNode = node.nextSibling;
            let offset = 0;
            if (!targetNode || targetNode.nodeType !== Node.TEXT_NODE) {
                targetNode = document.createTextNode('');
                parent.insertBefore(targetNode, node.nextSibling);
            }
            const range = document.createRange();
            range.setStart(targetNode, offset);
            range.collapse(true);
            const sel = window.getSelection();
            sel?.removeAllRanges();
            sel?.addRange(range);
        }

        placeCaretBeforeNode(node) {
            if (!node || !node.parentNode) return;
            const parent = node.parentNode;
            let targetNode = node.previousSibling;
            let offset = 0;
            if (!targetNode || targetNode.nodeType !== Node.TEXT_NODE) {
                targetNode = document.createTextNode('');
                parent.insertBefore(targetNode, node);
                offset = 0;
            } else {
                offset = targetNode.length;
            }
            const range = document.createRange();
            range.setStart(targetNode, offset);
            range.collapse(true);
            const sel = window.getSelection();
            sel?.removeAllRanges();
            sel?.addRange(range);
        }

        focusBlock(blockEl, atStart = true) {
            if (!blockEl) return;
            blockEl.focus();

            const range = document.createRange();
            const sel = window.getSelection();

            if (atStart) {
                if (blockEl.childNodes.length === 0) {
                    range.setStart(blockEl, 0);
                } else {
                    const firstChild = blockEl.firstChild;
                    if (firstChild.nodeType === Node.TEXT_NODE) {
                        range.setStart(firstChild, 0);
                    } else if (firstChild.tagName && firstChild.tagName.toLowerCase() === 'br') {
                        range.setStartBefore(firstChild);
                    } else {
                        range.setStart(blockEl, 0);
                    }
                }
                range.collapse(true);
            } else {
                if (blockEl.childNodes.length === 0) {
                    range.setStart(blockEl, 0);
                    range.collapse(true);
                } else {
                    const lastChild = blockEl.lastChild;
                    if (lastChild.nodeType === Node.TEXT_NODE) {
                        range.setStart(lastChild, lastChild.length);
                        range.collapse(true);
                    } else if (lastChild.tagName && lastChild.tagName.toLowerCase() === 'br') {
                        range.setStartBefore(lastChild);
                        range.collapse(true);
                    } else {
                        range.selectNodeContents(blockEl);
                        range.collapse(false);
                    }
                }
            }

            sel?.removeAllRanges();
            sel?.addRange(range);
        }

        isCaretAtStart(element) {
            if (!element) return false;
            const sel = window.getSelection();
            if (!sel || !sel.rangeCount) return false;
            const range = sel.getRangeAt(0);
            if (!range.collapsed) return false;
            if (!element.contains(range.startContainer)) return false;

            const testRange = document.createRange();
            testRange.setStart(element, 0);
            testRange.setEnd(range.startContainer, range.startOffset);
            const frag = testRange.cloneContents();
            const text = (frag.textContent || '').replace(/\r?\n/g, '');
            if (text.length > 0) return false;
            if (frag.querySelector && (frag.querySelector('.inline-math, .inline-graph') || frag.querySelector('img') || frag.querySelector('br'))) return false;
            return true;
        }

        isCaretAtEnd(element) {
            if (!element) return false;
            const sel = window.getSelection();
            if (!sel || !sel.rangeCount) return false;
            const range = sel.getRangeAt(0);
            if (!range.collapsed) return false;
            if (!element.contains(range.endContainer)) return false;

            const testRange = document.createRange();
            testRange.setStart(range.endContainer, range.endOffset);
            testRange.setEnd(element, element.childNodes.length);
            const frag = testRange.cloneContents();
            const text = (frag.textContent || '').replace(/\r?\n/g, '');
            if (text.length > 0) return false;
            if (frag.querySelector && (frag.querySelector('.inline-math, .inline-graph') || frag.querySelector('img') || frag.querySelector('br'))) return false;
            return true;
        }

        getCurrentBlock(textEl) {
            const sel = window.getSelection();
            if (!sel || !sel.rangeCount) return null;
            let node = sel.getRangeAt(0).startContainer;
            while (node && node.parentNode !== textEl) {
                node = node.parentNode;
            }
            return (node && node.parentNode === textEl) ? node : null;
        }

        normalizeBlocks(textEl) {
            if (!textEl) return;
            if (!textEl.childNodes.length) {
                textEl.innerHTML = '<p><br></p>';
                return;
            }

            let needsWrap = false;
            for (let node of textEl.childNodes) {
                if (node.nodeType === Node.TEXT_NODE) {
                    if (node.nodeValue.trim().length > 0) {
                        needsWrap = true;
                        break;
                    }
                } else if (node.nodeType === Node.ELEMENT_NODE) {
                    const tag = node.tagName.toLowerCase();
                    if (tag !== 'p' && !node.classList.contains('bullet-item')) {
                        needsWrap = true;
                        break;
                    }
                }
            }

            if (needsWrap) {
                const newChildren = [];
                let currentInlineNodes = [];

                const flushInline = () => {
                    if (currentInlineNodes.length > 0) {
                        const p = document.createElement('p');
                        currentInlineNodes.forEach(n => p.appendChild(n));
                        if (!p.childNodes.length || (p.textContent === '' && !p.querySelector('.inline-math, .inline-graph'))) {
                            p.innerHTML = '<br>';
                        }
                        newChildren.push(p);
                        currentInlineNodes = [];
                    }
                };

                Array.from(textEl.childNodes).forEach(node => {
                    if (node.nodeType === Node.ELEMENT_NODE && (node.tagName.toLowerCase() === 'p' || node.classList.contains('bullet-item'))) {
                        flushInline();
                        newChildren.push(node);
                    } else if (node.nodeType === Node.ELEMENT_NODE && node.tagName.toLowerCase() === 'br') {
                        flushInline();
                    } else {
                        currentInlineNodes.push(node);
                    }
                });
                flushInline();

                textEl.innerHTML = '';
                newChildren.forEach(child => textEl.appendChild(child));
            }

            if (!textEl.children.length) {
                textEl.innerHTML = '<p><br></p>';
            }
        }

        placeCaretAtEnd(el) {
            el.focus();
            this.normalizeBlocks(el);
            const lastChild = el.lastElementChild;
            if (!lastChild) {
                this.placeCaretAtNodeEnd(el);
                return;
            }
            const target = lastChild.classList.contains('bullet-item') ? 
                (lastChild.querySelector('.bullet-content') || lastChild) : lastChild;
            this.focusBlock(target, false);
        }

        placeCaretAtPoint(textEl, x, y) {
            textEl.focus();
            let range = null;
            if (document.caretPositionFromPoint) {
                const pos = document.caretPositionFromPoint(x, y);
                if (pos && pos.offsetNode && textEl.contains(pos.offsetNode)) {
                    range = document.createRange();
                    range.setStart(pos.offsetNode, pos.offset);
                    range.collapse(true);
                }
            } else if (document.caretRangeFromPoint) {
                const r = document.caretRangeFromPoint(x, y);
                if (r && textEl.contains(r.startContainer)) {
                    range = r;
                }
            }

            const sel = window.getSelection();
            sel?.removeAllRanges();
            if (range) {
                if (range.startContainer === textEl) {
                    const block = textEl.children[range.startOffset] || textEl.lastElementChild;
                    if (block) {
                        const target = block.classList.contains('bullet-item') ?
                            (block.querySelector('.bullet-content') || block) : block;
                        this.focusBlock(target, false);
                        return;
                    }
                }
                sel?.addRange(range);
            } else {
                this.placeCaretAtEnd(textEl);
            }
        }

        insertSoftLineBreakAtCaret(textEl) {
            const sel = window.getSelection();
            if (!sel || !sel.rangeCount) return;
            const range = sel.getRangeAt(0);
            range.deleteContents();

            let targetContainer = null;
            let node = range.startContainer;
            while (node && node !== textEl) {
                if (node.nodeType === Node.ELEMENT_NODE) {
                    if (node.classList?.contains('bullet-content') || node.tagName === 'P') {
                        targetContainer = node;
                        break;
                    }
                }
                node = node.parentNode;
            }

            if (!targetContainer) {
                this.insertParagraphBreakAtCaret(textEl);
                return;
            }

            const br = document.createElement('br');
            range.insertNode(br);

            // br 뒤에 시각적 콘텐츠가 있는지 확인
            let isTrailing = true;
            let next = br.nextSibling;
            while (next) {
                if (next.nodeType === Node.TEXT_NODE && next.nodeValue && next.nodeValue.length > 0) {
                    isTrailing = false;
                    break;
                }
                if (next.nodeType === Node.ELEMENT_NODE && !next.classList?.contains('trailing-soft-br')) {
                    isTrailing = false;
                    break;
                }
                next = next.nextSibling;
            }

            if (isTrailing) {
                const dummy = document.createElement('br');
                dummy.className = 'trailing-soft-br';
                br.after(dummy);
            }

            const newRange = document.createRange();
            newRange.setStartAfter(br);
            newRange.collapse(true);
            sel.removeAllRanges();
            sel.addRange(newRange);
        }

        insertParagraphBreakAtCaret(textEl) {
            const sel = window.getSelection();
            if (!sel || !sel.rangeCount) return;
            const range = sel.getRangeAt(0);
            range.deleteContents();

            let currentBlock = this.getCurrentBlock(textEl);
            if (!currentBlock) {
                const newP = document.createElement('p');
                newP.innerHTML = '<br>';
                textEl.appendChild(newP);
                this.focusBlock(newP, true);
                return;
            }

            const splitRange = document.createRange();
            splitRange.setStart(range.startContainer, range.startOffset);
            splitRange.setEnd(currentBlock, currentBlock.childNodes.length);
            const extractedFrag = splitRange.extractContents();

            const newP = document.createElement('p');
            if (currentBlock.style.textAlign) {
                newP.style.textAlign = currentBlock.style.textAlign;
            }
            if (currentBlock.style.paddingLeft) {
                newP.style.paddingLeft = currentBlock.style.paddingLeft;
            }

            const hasText = extractedFrag.textContent && extractedFrag.textContent.length > 0;
            const hasMath = extractedFrag.querySelector && !!extractedFrag.querySelector('.inline-math, .inline-graph');

            if (hasText || hasMath) {
                newP.appendChild(extractedFrag);
            } else {
                newP.innerHTML = '<br>';
            }

            const curHasText = currentBlock.textContent && currentBlock.textContent.length > 0;
            const curHasMath = currentBlock.querySelector && !!currentBlock.querySelector('.inline-math, .inline-graph');
            if (!curHasText && !curHasMath) {
                currentBlock.innerHTML = '<br>';
            } else {
                const last = currentBlock.lastChild;
                if (last && last.nodeType === Node.ELEMENT_NODE && last.tagName.toLowerCase() === 'br' && currentBlock.childNodes.length > 1) {
                    last.remove();
                }
            }

            currentBlock.after(newP);
            this.focusBlock(newP, true);
        }

        handleBackspaceAtCaret(textEl, e) {
            const sel = window.getSelection();
            if (!sel || !sel.rangeCount) return;
            const range = sel.getRangeAt(0);

            if (!range.collapsed) return;

            // 0. 문단 내 soft break (<br>) 직후에서 Backspace를 누른 경우: 해당 <br> 삭제
            let prevNode = null;
            if (range.startContainer.nodeType === Node.TEXT_NODE && range.startOffset === 0) {
                prevNode = range.startContainer.previousSibling;
            } else if (range.startContainer.nodeType === Node.ELEMENT_NODE && range.startOffset > 0) {
                prevNode = range.startContainer.childNodes[range.startOffset - 1];
            }

            if (prevNode && prevNode.nodeType === Node.ELEMENT_NODE && prevNode.tagName.toLowerCase() === 'br') {
                e.preventDefault();
                e.stopPropagation();

                const parent = prevNode.parentNode;
                const nextNode = prevNode.nextSibling;
                if (nextNode && nextNode.nodeType === Node.ELEMENT_NODE && nextNode.classList?.contains('trailing-soft-br')) {
                    nextNode.remove();
                }

                const prevSiblingOfBr = prevNode.previousSibling;
                prevNode.remove();

                const newRange = document.createRange();
                if (prevSiblingOfBr) {
                    if (prevSiblingOfBr.nodeType === Node.TEXT_NODE) {
                        newRange.setStart(prevSiblingOfBr, prevSiblingOfBr.length);
                    } else {
                        newRange.setStartAfter(prevSiblingOfBr);
                    }
                } else {
                    newRange.setStart(parent, 0);
                }
                newRange.collapse(true);
                sel.removeAllRanges();
                sel.addRange(newRange);
                return;
            }

            const currentBlock = this.getCurrentBlock(textEl);
            if (!currentBlock) return;

            if (currentBlock.classList.contains('bullet-item')) {
                const contentEl = currentBlock.querySelector('.bullet-content');
                if (contentEl && this.isCaretAtStart(contentEl)) {
                    e.preventDefault();
                    e.stopPropagation();
                    this.removeBulletItem(currentBlock);
                }
                return;
            }

            if (!this.isCaretAtStart(currentBlock)) {
                return;
            }

            const prevBlock = currentBlock.previousElementSibling;
            if (!prevBlock) {
                e.preventDefault();
                return;
            }

            e.preventDefault();
            e.stopPropagation();

            const isCurEmpty = (!currentBlock.textContent || currentBlock.textContent.trim() === '') && !currentBlock.querySelector('.inline-math, .inline-graph');
            const targetPrev = prevBlock.classList.contains('bullet-item') ? 
                (prevBlock.querySelector('.bullet-content') || prevBlock) : prevBlock;

            if (isCurEmpty) {
                currentBlock.remove();
                this.focusBlock(targetPrev, false);
                return;
            }

            const isPrevEmpty = (!targetPrev.textContent || targetPrev.textContent.trim() === '') && !targetPrev.querySelector('.inline-math, .inline-graph');
            if (isPrevEmpty && prevBlock.tagName === 'P') {
                prevBlock.remove();
                this.focusBlock(currentBlock, true);
                return;
            }

            if (targetPrev.childNodes.length === 1 && targetPrev.firstChild.nodeName === 'BR') {
                targetPrev.innerHTML = '';
            } else if (targetPrev.lastChild && targetPrev.lastChild.nodeName === 'BR') {
                targetPrev.lastChild.remove();
            }

            const firstMovedChild = currentBlock.firstChild;
            while (currentBlock.firstChild) {
                targetPrev.appendChild(currentBlock.firstChild);
            }
            currentBlock.remove();

            if (firstMovedChild) {
                if (firstMovedChild.nodeType === Node.TEXT_NODE) {
                    const r = document.createRange();
                    r.setStart(firstMovedChild, 0);
                    r.collapse(true);
                    sel.removeAllRanges();
                    sel.addRange(r);
                } else {
                    this.focusBlock(firstMovedChild, true);
                }
            } else {
                this.focusBlock(targetPrev, false);
            }
        }

        handleDeleteAtCaret(textEl, e) {
            const sel = window.getSelection();
            if (!sel || !sel.rangeCount) return;
            const range = sel.getRangeAt(0);
            if (!range.collapsed) return;

            // 0. 문단 내 soft break (<br>) 직전에서 Delete를 누른 경우: 해당 <br> 삭제
            let nextNode = null;
            if (range.startContainer.nodeType === Node.TEXT_NODE && range.startOffset === range.startContainer.length) {
                nextNode = range.startContainer.nextSibling;
            } else if (range.startContainer.nodeType === Node.ELEMENT_NODE && range.startOffset < range.startContainer.childNodes.length) {
                nextNode = range.startContainer.childNodes[range.startOffset];
            }

            if (nextNode && nextNode.nodeType === Node.ELEMENT_NODE && nextNode.tagName.toLowerCase() === 'br') {
                e.preventDefault();
                e.stopPropagation();
                const trailing = nextNode.nextSibling;
                if (trailing && trailing.nodeType === Node.ELEMENT_NODE && trailing.classList?.contains('trailing-soft-br')) {
                    trailing.remove();
                }
                nextNode.remove();
                return;
            }

            const currentBlock = this.getCurrentBlock(textEl);
            if (!currentBlock) return;

            const targetCurrent = currentBlock.classList.contains('bullet-item') ?
                (currentBlock.querySelector('.bullet-content') || currentBlock) : currentBlock;

            if (!this.isCaretAtEnd(targetCurrent)) return;

            const nextBlock = currentBlock.nextElementSibling;
            if (!nextBlock) return;

            e.preventDefault();
            e.stopPropagation();

            const targetNext = nextBlock.classList.contains('bullet-item') ?
                (nextBlock.querySelector('.bullet-content') || nextBlock) : nextBlock;

            const isNextEmpty = (!targetNext.textContent || targetNext.textContent.trim() === '') && !targetNext.querySelector('.inline-math, .inline-graph');

            if (isNextEmpty) {
                nextBlock.remove();
                return;
            }

            if (targetCurrent.childNodes.length === 1 && targetCurrent.firstChild.nodeName === 'BR') {
                targetCurrent.innerHTML = '';
            }

            const firstMovedChild = targetNext.firstChild;
            while (targetNext.firstChild) {
                targetCurrent.appendChild(targetNext.firstChild);
            }
            nextBlock.remove();

            if (firstMovedChild) {
                if (firstMovedChild.nodeType === Node.TEXT_NODE) {
                    const r = document.createRange();
                    r.setStart(firstMovedChild, 0);
                    r.collapse(true);
                    sel.removeAllRanges();
                    sel.addRange(r);
                } else {
                    this.focusBlock(firstMovedChild, true);
                }
            }
        }

        cleanHtmlLineBreaks(html) {
            return cleanHtmlLineBreaks(html);
        }

        bindTextEvents(textEl, boxEl) {
            if (textEl._hasEditListeners) return;
            textEl._hasEditListeners = true;

            textEl.addEventListener('keydown', (e) => {

                // 0. Tab / Shift+Tab 키: 문단 및 글머리 기호 들여쓰기(Tab: +1em) / 내어쓰기(Shift+Tab: -1em)
                if (e.key === 'Tab') {
                    e.preventDefault();
                    e.stopPropagation();
                    this.applyIndent(e.shiftKey ? -1 : 1);
                    return;
                }

                // 0-1. Alt+Down / Alt+Up 키: 문단 및 글머리 기호 아래 여백 조절 (+0.25em / -0.25em, 범위: -2.0em ~ +2.0em)
                if (e.altKey && !e.ctrlKey && !e.metaKey && !e.shiftKey) {
                    if (e.key === 'ArrowDown') {
                        e.preventDefault();
                        e.stopPropagation();
                        this.applyBottomMargin(0.25);
                        return;
                    }
                    if (e.key === 'ArrowUp') {
                        e.preventDefault();
                        e.stopPropagation();
                        this.applyBottomMargin(-0.25);
                        return;
                    }
                }

                // 1. Shift+4 또는 $ 키: 수식 추가 트리거
                if ((e.shiftKey && (e.code === 'Digit4' || e.key === '$')) || e.key === '$') {
                    e.preventDefault();
                    e.stopPropagation();
                    this.insertNewMathAtCaret();
                    return;
                }

                // 2. ArrowRight: 수식 또는 그래프 바로 왼쪽에서 오른쪽 방향키 누르면 버블 진입 (start 위치)
                if (e.key === 'ArrowRight') {
                    const nextMath = this.getNextSiblingInlineMath();
                    if (nextMath) {
                        e.preventDefault();
                        e.stopPropagation();
                        this.activateMathBubble(nextMath, 'start');
                        return;
                    }
                    const nextGraph = this.getNextSiblingInlineGraph();
                    if (nextGraph) {
                        e.preventDefault();
                        e.stopPropagation();
                        this.activateGraphBubble(nextGraph, 'start');
                        return;
                    }
                }

                // 3. ArrowLeft: 수식 또는 그래프 바로 오른쪽에서 왼쪽 방향키 누르면 버블 진입 (end 위치)
                if (e.key === 'ArrowLeft') {
                    const prevMath = this.getPrevSiblingInlineMath();
                    if (prevMath) {
                        e.preventDefault();
                        e.stopPropagation();
                        this.activateMathBubble(prevMath, 'end');
                        return;
                    }
                    const prevGraph = this.getPrevSiblingInlineGraph();
                    if (prevGraph) {
                        e.preventDefault();
                        e.stopPropagation();
                        this.activateGraphBubble(prevGraph, 'end');
                        return;
                    }
                }

                // 4. Enter 키: Shift+Enter(같은 문단 내 줄바꿈) vs Enter(새 문단 블록/새 글머리 기호)
                if (e.key === 'Enter') {
                    if (e.shiftKey) {
                        e.preventDefault();
                        e.stopPropagation();
                        this.insertSoftLineBreakAtCaret(textEl);
                        return;
                    }

                    const currentBullet = this.getCurrentBulletItem();
                    if (currentBullet) {
                        e.preventDefault();
                        e.stopPropagation();
                        this.handleBulletEnter(currentBullet);
                        return;
                    }
                    e.preventDefault();
                    e.stopPropagation();
                    this.insertParagraphBreakAtCaret(textEl);
                    return;
                }

                // 4-2. Backspace 키: 글머리 기호 삭제 또는 이전 문단과의 병합/빈 문단 삭제
                if (e.key === 'Backspace') {
                    this.handleBackspaceAtCaret(textEl, e);
                    return;
                }

                // 4-3. Delete 키: 문단 끝에서 다음 문단과의 병합
                if (e.key === 'Delete') {
                    this.handleDeleteAtCaret(textEl, e);
                    return;
                }

                // 5. Esc: 편집 종료 및 커밋
                if (e.key === 'Escape') {
                    e.preventDefault();
                    e.stopPropagation();
                    this.stopEditing(boxEl);
                    return;
                }

                // 6. 문단 정렬 단축키 (Ctrl+L: 왼쪽, Ctrl+E / Ctrl+C: 가운데, Ctrl+R: 오른쪽)
                if ((e.ctrlKey || e.metaKey) && !e.altKey) {
                    const key = e.key.toLowerCase();
                    if (key === 'l') {
                        e.preventDefault();
                        e.stopPropagation();
                        this.applyAlignment('left');
                        return;
                    }
                    if (key === 'e' || key === 'c') {
                        e.preventDefault();
                        e.stopPropagation();
                        this.applyAlignment('center');
                        return;
                    }
                    if (key === 'r') {
                        e.preventDefault();
                        e.stopPropagation();
                        this.applyAlignment('right');
                        return;
                    }
                }

                // 7. 서식 단축키 (Ctrl+B: 굵게, Ctrl+I: 기울임, Ctrl+U: 밑줄)
                if ((e.ctrlKey || e.metaKey) && !e.shiftKey && !e.altKey) {
                    const key = e.key.toLowerCase();
                    if (key === 'b') {
                        e.preventDefault();
                        e.stopPropagation();
                        this.applyFormat('bold');
                        return;
                    }
                    if (key === 'i') {
                        e.preventDefault();
                        e.stopPropagation();
                        this.applyFormat('italic');
                        return;
                    }
                    if (key === 'u') {
                        e.preventDefault();
                        e.stopPropagation();
                        this.applyFormat('underline');
                        return;
                    }
                }
            });

            // 붙여넣기 시 문단 블록(<p>) 구조에 맞게 순수 텍스트 줄바꿈 분할 삽입
            textEl.addEventListener('paste', (e) => {
                e.preventDefault();
                const pasteText = (e.clipboardData || window.clipboardData)?.getData('text/plain') || '';
                if (!pasteText) return;

                const lines = pasteText.split(/\r?\n/);
                if (lines.length === 1) {
                    document.execCommand('insertText', false, lines[0]);
                } else {
                    for (let i = 0; i < lines.length; i++) {
                        if (i > 0) {
                            this.insertParagraphBreakAtCaret(textEl);
                        }
                        if (lines[i]) {
                            document.execCommand('insertText', false, lines[i]);
                        }
                    }
                }
            });
        }

        startEditing(boxEl, clientX, clientY) {
            if (!boxEl || boxEl.classList.contains('is-editing')) return;

            if (this.activeBox && this.activeBox !== boxEl) {
                this.stopEditing(this.activeBox);
            }

            if (this.historyManager) {
                this.textEditingInitialSnapshot = this.historyManager.captureSnapshot();
            }

            this.activeBox = boxEl;
            boxEl.classList.add('is-editing');

            const textEl = boxEl.querySelector('.box-text');
            if (!textEl) return;

            const item = this.store.elementsMap.get(boxEl.id);
            if (item && !item.isRendered) {
                this.store.renderSingleBox(item);
            }
            const initialText = (item && item.text !== undefined) ? item.text : '';

            // 편집 모드 진입 시 기존 렌더링된 자식이 없는 경우에만 초기 파싱 수행
            textEl.contentEditable = 'true';
            if (!textEl.childNodes.length) {
                textEl.innerHTML = parseMathToHtml(initialText);
            }
            this.normalizeBlocks(textEl);

            this.bindTextEvents(textEl, boxEl);
            this.initMathInContainer(textEl);
            this.initGraphInContainer(textEl);
            this.initBulletsInContainer(textEl);

            if (clientX !== undefined && clientY !== undefined) {
                this.placeCaretAtPoint(textEl, clientX, clientY);
            } else {
                this.placeCaretAtEnd(textEl);
            }

            window.startBoxTextEditingGlobal = (b) => this.startEditing(b);
        }

        stopEditing(boxEl = this.activeBox) {
            if (!boxEl || !boxEl.classList.contains('is-editing')) return;

            if (this.activeMathTarget) {
                this.deactivateMathBubble(true, 'none');
            }
            if (this.activeGraphTarget) {
                this.deactivateGraphBubble(true, 'none');
            }
            if (this.activeMarkerTarget) {
                this.deactivateMarkerBubble(true);
            }

            boxEl.classList.remove('is-editing');
            const textEl = boxEl.querySelector('.box-text');

            let newText = '';
            if (textEl) {
                textEl.contentEditable = 'false';
                newText = serializeHtmlToText(textEl);
            }

            window.getSelection()?.removeAllRanges();

            const item = this.store.elementsMap.get(boxEl.id);
            if (item) {
                item.text = newText;
                // 중요: 편집 모드 해제 시 DOM(textEl.innerHTML)을 다시 파싱/재렌더링하여 변형하지 않고 그대로 유지
            }

            if (this.textEditingInitialSnapshot && this.historyManager) {
                this.historyManager.pushUndoSnapshot(this.textEditingInitialSnapshot);
                this.textEditingInitialSnapshot = null;
            }

            if (this.activeBox === boxEl) {
                this.activeBox = null;
            }
        }
    }

    // =========================================================================
    // 7. 생성 모드 관리자 (Add Mode Manager)
    // =========================================================================
    class AddModeManager {
        constructor(store, selectionManager, textEditor) {
            this.store = store;
            this.selectionManager = selectionManager;
            this.textEditor = textEditor;
            this.currentMode = null; // 'box' | 'line' | null
            this.interactionManager = null;

            this.cancelBtn = document.getElementById('add-mode-cancel-btn');
            this.addBoxBtn = document.getElementById('add-box-btn');
            this.addLineBtn = document.getElementById('add-line-btn');

            this.init();
        }

        init() {
            if (this.cancelBtn) {
                this.cancelBtn.addEventListener('click', (e) => {
                    e.stopPropagation();
                    e.preventDefault();
                    this.setMode(null);
                });
                this.cancelBtn.addEventListener('pointerdown', (e) => {
                    e.stopPropagation();
                });
            }

            if (this.addBoxBtn) {
                this.addBoxBtn.addEventListener('click', (e) => {
                    e.stopPropagation();
                    this.setMode(this.currentMode === 'box' ? null : 'box');
                });
            }

            if (this.addLineBtn) {
                this.addLineBtn.addEventListener('click', (e) => {
                    e.stopPropagation();
                    this.setMode(this.currentMode === 'line' ? null : 'line');
                });
            }
        }

        setMode(mode) {
            this.currentMode = mode;
            if (mode === 'box' || mode === 'line') {
                if (this.selectionManager) {
                    this.selectionManager.clear();
                }
                document.body.classList.add('add-mode-active');
                if (mode === 'box') {
                    this.addBoxBtn?.classList.add('active');
                    this.addLineBtn?.classList.remove('active');
                } else {
                    this.addLineBtn?.classList.add('active');
                    this.addBoxBtn?.classList.remove('active');
                }
            } else {
                this.currentMode = null;
                document.body.classList.remove('add-mode-active');
                this.addBoxBtn?.classList.remove('active');
                this.addLineBtn?.classList.remove('active');

                // 진행 중이던 그리기 프리뷰 정리
                if (this.interactionManager) {
                    this.interactionManager.cancelDraw();
                }
            }
        }
    }

    // =========================================================================
    // 8. 통합 인터랙션 관리자 (Interaction & Transform Manager)
    //    - 휠 클릭 이동(Pan)
    //    - 빈 공간 드래그 시 사각형 영역 선택(Marquee)
    //    - 선택된 박스 드래그 다중 이동
    //    - 박스 에지 리사이즈 핸들 드래그 크기 조절
    //    - 더블클릭 / Enter 텍스트 편집
    // =========================================================================
    class InteractionManager {
        constructor(viewport, store, selectionManager, textEditor, addModeManager, historyManager = null, dataManager = null) {
            this.viewport = viewport;
            this.store = store;
            this.selectionManager = selectionManager;
            this.textEditor = textEditor;
            this.addModeManager = addModeManager;
            this.historyManager = historyManager;
            this.dataManager = dataManager;

            // 드래그 생성 상태 { type, pointerId, startCellX, startCellY, element }
            this.drawInfo = null;

            // 마키 영역 선택 DOM
            this.marqueeEl = document.getElementById('selection-marquee');

            // 캔버스 컨텍스트 메뉴 (우클릭 / 터치 롱프레스)
            this.contextMenuEl = document.getElementById('canvas-context-menu');
            this.contextMenuGridPos = { x: 0, y: 0 };
            this.longPressTimer = null;
            this.touchStartPos = { x: 0, y: 0 };

            // 터치 2손가락 핀치 줌 / 패닝 제스처 상태
            this.activeTouches = new Map();
            this.touchStartData = null;

            this.bindEvents();
        }

        getTouchMidpointAndDistance() {
            const points = Array.from(this.activeTouches.values());
            if (points.length < 2) return null;
            const p1 = points[0];
            const p2 = points[1];
            return {
                midX: (p1.clientX + p2.clientX) / 2,
                midY: (p1.clientY + p2.clientY) / 2,
                distance: Math.hypot(p2.clientX - p1.clientX, p2.clientY - p1.clientY)
            };
        }

        cancelDraw() {
            if (this.drawInfo) {
                if (this.drawInfo.pointerId !== undefined) {
                    try { document.body.releasePointerCapture(this.drawInfo.pointerId); } catch (_) {}
                }
                if (this.drawInfo.element) {
                    this.drawInfo.element.remove();
                }
                this.drawInfo = null;
                this.viewport.hideTooltip();
            }
        }

        showContextMenu(clientX, clientY, targetMode = 'canvas', hasSelection = false) {
            if (!this.contextMenuEl) return;
            const gridPos = this.viewport.screenToGrid(clientX, clientY);
            this.contextMenuGridPos = gridPos;

            const canvasItems = document.getElementById('ctx-canvas-items');
            const objectItems = document.getElementById('ctx-object-items');
            const textItems = document.getElementById('ctx-text-items');
            const formatGroup = document.getElementById('ctx-text-format-group');

            if (canvasItems) canvasItems.style.display = 'none';
            if (objectItems) objectItems.style.display = 'none';
            if (textItems) textItems.style.display = 'none';

            if (targetMode === 'object') {
                if (objectItems) objectItems.style.display = 'block';
            } else if (targetMode === 'text') {
                if (textItems) {
                    textItems.style.display = 'block';
                    if (formatGroup) {
                        formatGroup.style.display = hasSelection ? 'block' : 'none';
                    }
                }
            } else {
                if (canvasItems) canvasItems.style.display = 'block';
            }

            let posX = clientX;
            let posY = clientY;

            this.contextMenuEl.style.left = `${posX}px`;
            this.contextMenuEl.style.top = `${posY}px`;
            this.contextMenuEl.classList.add('show');

            const menuRect = this.contextMenuEl.getBoundingClientRect();
            if (posX + menuRect.width > window.innerWidth - 10) {
                posX = Math.max(10, window.innerWidth - menuRect.width - 10);
            }
            if (posY + menuRect.height > window.innerHeight - 10) {
                posY = Math.max(10, window.innerHeight - menuRect.height - 10);
            }
            this.contextMenuEl.style.left = `${posX}px`;
            this.contextMenuEl.style.top = `${posY}px`;
        }

        hideContextMenu() {
            if (this.contextMenuEl) {
                this.contextMenuEl.classList.remove('show');
            }
        }

        bindEvents() {
            // 박스 더블클릭 -> 글쓰기(편집) 모드 진입 (수식 더블클릭 시 수식 수정 버블, 마커 더블클릭 시 기호 수정 버블 활성화)
            window.addEventListener('dblclick', (e) => {
                const box = e.target.closest('.box');
                if (box) {
                    e.preventDefault();
                    this.selectionManager.select(box);
                    this.textEditor.startEditing(box, e.clientX, e.clientY);

                    const clickedMath = e.target.closest('.inline-math');
                    if (clickedMath) {
                        this.textEditor.activateMathBubble(clickedMath, 'end');
                    }
                    const clickedGraph = e.target.closest('.inline-graph');
                    if (clickedGraph) {
                        this.textEditor.activateGraphBubble(clickedGraph, 'end');
                    }
                    const clickedMarker = e.target.closest('.bullet-marker');
                    if (clickedMarker) {
                        this.textEditor.activateMarkerBubble(clickedMarker);
                    }
                }
            });

            // 마우스 우클릭 -> 캔버스, 개체 및 텍스트 편집 컨텍스트 메뉴
            window.addEventListener('contextmenu', (e) => {
                if (e.target.closest('#canvas-context-menu, #math-mini-code-bubble, #graph-mini-code-bubble, #marker-mini-bubble, .modal-overlay')) {
                    e.preventDefault();
                    return;
                }

                // 텍스트 편집 중인 박스 내부에서 우클릭한 경우: 텍스트 컨텍스트 메뉴 (수식 추가, 서식)
                const editingBox = e.target.closest('.box.is-editing');
                if (editingBox) {
                    e.preventDefault();
                    const textEl = editingBox.querySelector('.box-text');
                    const sel = window.getSelection();
                    let hasSelection = false;

                    if (sel && sel.rangeCount > 0 && !sel.isCollapsed) {
                        const range = sel.getRangeAt(0);
                        if (editingBox.contains(range.commonAncestorContainer)) {
                            hasSelection = true;
                            this.textEditor.savedSelectionRange = range.cloneRange();
                        }
                    }

                    if (!hasSelection && textEl) {
                        this.textEditor.placeCaretAtPoint(textEl, e.clientX, e.clientY);
                        const curSel = window.getSelection();
                        if (curSel && curSel.rangeCount > 0) {
                            this.textEditor.savedSelectionRange = curSel.getRangeAt(0).cloneRange();
                        }
                    }

                    this.showContextMenu(e.clientX, e.clientY, 'text', hasSelection);
                    return;
                }

                e.preventDefault();

                const clickedObject = e.target.closest('.box, .line');
                if (clickedObject) {
                    // 개체 위에서 우클릭한 경우: 이미 선택된 개체가 아니면 해당 개체만 단일 선택
                    const isAlreadySelected = this.selectionManager.selectedElements.has(clickedObject);
                    if (!isAlreadySelected) {
                        this.selectionManager.select(clickedObject, false);
                    }
                    // 이미 선택되어 있는 경우(단일 또는 다중)는 기존 선택 상태 유지
                    this.showContextMenu(e.clientX, e.clientY, 'object');
                } else {
                    // 빈 캔버스 위에서 우클릭한 경우 (박스 생성, 선 생성)
                    this.showContextMenu(e.clientX, e.clientY, 'canvas');
                }
            });

            // 컨텍스트 메뉴 클릭 동작 (박스 생성 / 선 생성 / 선택 개체 삭제 / 서식 적용 / 수식 추가)
            if (this.contextMenuEl) {
                // 포인터 다운 및 마우스 다운 시 캔버스 제스처로 전파 방지 및 텍스트 선택 해제 방지
                this.contextMenuEl.addEventListener('pointerdown', (e) => {
                    e.stopPropagation();
                });
                this.contextMenuEl.addEventListener('mousedown', (e) => {
                    e.preventDefault();
                    e.stopPropagation();
                });

                let lastActionTime = 0;
                const handleAction = (e) => {
                    const now = Date.now();
                    if (now - lastActionTime < 150) return;
                    lastActionTime = now;

                    const item = e.target.closest('.menu-item');
                    if (!item) return;

                    e.stopPropagation();
                    e.preventDefault();

                    const action = item.dataset.action;

                    if (action === 'undo') {
                        if (this.textEditor && this.textEditor.activeBox) {
                            const textEl = this.textEditor.activeBox.querySelector('.box-text');
                            if (textEl) {
                                textEl.focus();
                                if (this.textEditor.savedSelectionRange) {
                                    const s = window.getSelection();
                                    s.removeAllRanges();
                                    s.addRange(this.textEditor.savedSelectionRange);
                                }
                            }
                            document.execCommand('undo');
                        } else {
                            if (this.historyManager) this.historyManager.undo();
                        }
                    } else if (action === 'redo') {
                        if (this.textEditor && this.textEditor.activeBox) {
                            const textEl = this.textEditor.activeBox.querySelector('.box-text');
                            if (textEl) {
                                textEl.focus();
                                if (this.textEditor.savedSelectionRange) {
                                    const s = window.getSelection();
                                    s.removeAllRanges();
                                    s.addRange(this.textEditor.savedSelectionRange);
                                }
                            }
                            document.execCommand('redo');
                        } else {
                            if (this.historyManager) this.historyManager.redo();
                        }
                    } else if (action === 'create-box') {
                        this.addModeManager.setMode('box');
                    } else if (action === 'create-line') {
                        this.addModeManager.setMode('line');
                    } else if (action === 'delete-selected') {
                        this.selectionManager.deleteSelected(this.store, this.historyManager);
                    } else if (action === 'export-json') {
                        if (this.dataManager) this.dataManager.exportJsonFile();
                    } else if (action === 'cloud-settings') {
                        if (this.dataManager && this.dataManager.openCloudModal) {
                            this.dataManager.openCloudModal();
                        }
                    } else if (action === 'insert-math') {
                        this.textEditor.insertNewMathAtCaret();
                    } else if (action === 'insert-graph') {
                        this.textEditor.insertNewGraphAtCaret();
                    } else if (action === 'add-bullet') {
                        this.textEditor.insertBulletItem();
                    } else if (action === 'format-bold') {
                        this.textEditor.applyFormat('bold');
                    } else if (action === 'format-italic') {
                        this.textEditor.applyFormat('italic');
                    } else if (action === 'format-underline') {
                        this.textEditor.applyFormat('underline');
                    } else if (action === 'align-left') {
                        this.textEditor.applyAlignment('left');
                    } else if (action === 'align-center') {
                        this.textEditor.applyAlignment('center');
                    } else if (action === 'align-right') {
                        this.textEditor.applyAlignment('right');
                    } else if (action === 'indent') {
                        this.textEditor.applyIndent(1);
                    } else if (action === 'outdent') {
                        this.textEditor.applyIndent(-1);
                    } else if (action === 'margin-increase') {
                        this.textEditor.applyBottomMargin(0.25);
                    } else if (action === 'margin-decrease') {
                        this.textEditor.applyBottomMargin(-0.25);
                    }

                    this.hideContextMenu();
                };

                this.contextMenuEl.addEventListener('click', handleAction);
                this.contextMenuEl.addEventListener('pointerup', handleAction);
            }

            // 포인터 다운: 휠 패닝, 에지 리사이즈, 개체 이동, 영역 선택(Marquee)
            document.addEventListener('pointerdown', (e) => {
                // 컨텍스트 메뉴, 모달, 상태 뱃지, 또는 생성 취소 버튼 클릭 시 캔버스 동작 일체 차단
                if (e.target.closest('#canvas-context-menu, #add-mode-cancel-btn, #cloud-settings-modal, #cloud-status-indicator')) {
                    return;
                }

                // 컨텍스트 메뉴 바깥 클릭 시 닫기
                if (this.contextMenuEl && this.contextMenuEl.classList.contains('show')) {
                    this.hideContextMenu();
                }

                // 1. 휠 버튼(스크롤 클릭, button === 1): 화면 어디서든 패닝 시작
                if (e.button === 1) {
                    e.preventDefault();
                    this.viewport.isPanning = true;
                    this.viewport.panStartX = e.clientX;
                    this.viewport.panStartY = e.clientY;
                    this.viewport.startPanX = this.viewport.panX;
                    this.viewport.startPanY = this.viewport.panY;
                    document.body.classList.add('is-panning');
                    try { document.body.setPointerCapture(e.pointerId); } catch (_) {}
                    return;
                }

                // 터치 이벤트 관리 및 2손가락 핀치 줌 / 패닝 감지
                if (e.pointerType === 'touch') {
                    this.activeTouches.set(e.pointerId, { clientX: e.clientX, clientY: e.clientY });
                    if (this.activeTouches.size === 2) {
                        if (this.longPressTimer) {
                            clearTimeout(this.longPressTimer);
                            this.longPressTimer = null;
                        }
                        if (this.drawInfo) {
                            if (this.drawInfo.element) this.drawInfo.element.remove();
                            this.drawInfo = null;
                            this.viewport.hideTooltip();
                        }
                        if (this.marqueeData) {
                            if (this.marqueeEl) this.marqueeEl.style.display = 'none';
                            this.marqueeData = null;
                        }
                        const data = this.getTouchMidpointAndDistance();
                        if (data) {
                            this.touchStartData = {
                                initialMidX: data.midX,
                                initialMidY: data.midY,
                                initialDist: data.distance,
                                initialPanX: this.viewport.panX,
                                initialPanY: this.viewport.panY,
                                initialScale: this.viewport.scale
                            };
                        }
                        return;
                    }
                }

                // 터치 롱프레스 감지 (터치 디바이스 우클릭 대안, 500ms 유지 시 햅틱 및 메뉴 호출)
                if (e.pointerType === 'touch' && e.button === 0) {
                    const targetObject = e.target.closest('.box, .line');
                    this.touchStartPos = { x: e.clientX, y: e.clientY };
                    if (this.longPressTimer) clearTimeout(this.longPressTimer);
                    this.longPressTimer = setTimeout(() => {
                        this.longPressTimer = null;
                        try { navigator.vibrate?.(40); } catch (_) {}
                        if (this.marqueeData) {
                            if (this.marqueeEl) this.marqueeEl.style.display = 'none';
                            this.marqueeData = null;
                        }
                        if (targetObject) {
                            const isAlreadySelected = this.selectionManager.selectedElements.has(targetObject);
                            if (!isAlreadySelected) {
                                this.selectionManager.select(targetObject, false);
                            }
                            this.showContextMenu(this.touchStartPos.x, this.touchStartPos.y, 'object');
                        } else {
                            this.showContextMenu(this.touchStartPos.x, this.touchStartPos.y, 'canvas');
                        }
                    }, 500);
                }

                // 글머리 기호 버블 바깥 클릭 시 기호 변경 확정 및 버블 닫기
                if (this.textEditor.activeMarkerTarget && !e.target.closest('#marker-mini-bubble, .bullet-marker')) {
                    this.textEditor.deactivateMarkerBubble(true);
                }

                // 편집 중인 박스 바깥 클릭 시 편집 모드 커밋 및 종료 (수식 버블, 기호 버블 또는 컨텍스트 메뉴 클릭 시 유지)
                if (this.textEditor.activeBox && !this.textEditor.activeBox.contains(e.target) && !e.target.closest('#math-mini-code-bubble, #marker-mini-bubble, #canvas-context-menu')) {
                    this.textEditor.stopEditing(this.textEditor.activeBox);
                }

                // 상단 메뉴바 클릭 시 캔버스 동작 차단
                if (e.target.closest('#menu-bar')) return;

                // 텍스트 편집 중인 박스 내부 클릭 시: 커서 유지 및 빈 영역 클릭 시 포커스 보장
                const editingBox = e.target.closest('.box.is-editing');
                if (editingBox) {
                    const textEl = editingBox.querySelector('.box-text');
                    if (textEl && (!textEl.contains(e.target) || e.target === textEl)) {
                        // textEl 바깥의 박스 빈 공간 또는 textEl 내부의 빈 여백 클릭 시 포커스 유지 및 끝으로 커서 이동
                        e.preventDefault();
                        this.textEditor.placeCaretAtEnd(textEl);
                    }
                    return;
                }

                // 추가 모드 상태일 때: 마우스 좌클릭으로 박스 또는 선 드래그 생성 시작
                if (this.addModeManager.currentMode && e.button === 0) {
                    if (e.target.closest('#add-mode-cancel-btn')) return;

                    const canvasX = (e.clientX - this.viewport.panX) / this.viewport.scale;
                    const canvasY = (e.clientY - this.viewport.panY) / this.viewport.scale;
                    const startCellX = Math.max(0, Math.floor(canvasX / this.viewport.cellSize));
                    const startCellY = Math.max(0, Math.floor(canvasY / this.viewport.cellSize));

                    this.viewport.ensureGridSize(startCellX + 1, startCellY + 1);

                    if (this.historyManager) this.historyManager.recordActionStart();

                    if (this.addModeManager.currentMode === 'box') {
                        const boxDiv = this.store.createBoxPreview(startCellX, startCellY);
                        this.drawInfo = {
                            type: 'box',
                            pointerId: e.pointerId,
                            startCellX,
                            startCellY,
                            element: boxDiv
                        };
                        try { document.body.setPointerCapture(e.pointerId); } catch (_) {}
                        this.viewport.showTooltip(e.clientX + 14, e.clientY + 14, 'W: 1em, H: 1em', 0);
                        return;
                    } else if (this.addModeManager.currentMode === 'line') {
                        const lineDiv = this.store.createLinePreview(startCellX, startCellY);
                        this.drawInfo = {
                            type: 'line',
                            pointerId: e.pointerId,
                            startCellX,
                            startCellY,
                            element: lineDiv
                        };
                        try { document.body.setPointerCapture(e.pointerId); } catch (_) {}
                        this.viewport.showTooltip(e.clientX + 14, e.clientY + 14, 'W: 0em, H: 0em', 0);
                        return;
                    }
                }

                // 2-A. 선(Line) 끝점 핸들 클릭 (단일 선택된 Line) - Vertex Sharing(꼭짓점 공유) 준비
                const linePoint = e.target.closest('.line-point');
                if (linePoint && e.button === 0) {
                    const line = linePoint.closest('.line');
                    if (line && this.selectionManager.selectedElements.size === 1) {
                        e.stopPropagation();
                        e.preventDefault();
                        const pointType = linePoint.dataset.point; // 'start' | 'end'
                        const left = parseInt(line.dataset.left) || 0;
                        const top = parseInt(line.dataset.top) || 0;
                        const width = parseInt(line.dataset.width) || 0;
                        const height = parseInt(line.dataset.height) || 0;

                        const targetX = pointType === 'start' ? left : left + width;
                        const targetY = pointType === 'start' ? top : top + height;

                        // 공유된 다른 Line의 끝점 검색 (Vertex Sharing)
                        const connectedPoints = [];
                        this.store.elementsMap.forEach(item => {
                            if (item.type === 'line' && item.id !== line.id) {
                                const lLeft = item.left;
                                const lTop = item.top;
                                const lWidth = item.width;
                                const lHeight = item.height;

                                if (lLeft === targetX && lTop === targetY) {
                                    connectedPoints.push({
                                        element: item.element,
                                        id: item.id,
                                        pointType: 'start',
                                        startLeft: lLeft,
                                        startTop: lTop,
                                        startWidth: lWidth,
                                        startHeight: lHeight
                                    });
                                }
                                if ((lLeft + lWidth) === targetX && (lTop + lHeight) === targetY) {
                                    connectedPoints.push({
                                        element: item.element,
                                        id: item.id,
                                        pointType: 'end',
                                        startLeft: lLeft,
                                        startTop: lTop,
                                        startWidth: lWidth,
                                        startHeight: lHeight
                                    });
                                }
                            }
                        });

                        if (this.historyManager) this.historyManager.recordActionStart();

                        this.resizeData = {
                            type: 'line-point',
                            pointType,
                            element: line,
                            pointerId: e.pointerId,
                            startClientX: e.clientX,
                            startClientY: e.clientY,
                            startLeft: left,
                            startTop: top,
                            startWidth: width,
                            startHeight: height,
                            targetX,
                            targetY,
                            connectedPoints,
                            isDragging: false
                        };
                        try { document.body.setPointerCapture(e.pointerId); } catch (_) {}
                        return;
                    }
                }

                // 2-B. 박스 에지 리사이즈 핸들 클릭 (단일 선택된 박스)
                const edgeHandle = e.target.closest('.box-edge');
                if (edgeHandle && e.button === 0) {
                    const box = edgeHandle.closest('.box');
                    if (box && this.selectionManager.selectedElements.size === 1) {
                        e.stopPropagation();
                        e.preventDefault();
                        const edge = edgeHandle.dataset.edge;

                        if (this.historyManager) this.historyManager.recordActionStart();

                        this.resizeData = {
                            type: 'box-edge',
                            box,
                            edge,
                            startClientX: e.clientX,
                            startClientY: e.clientY,
                            startLeft: parseFloat(box.dataset.left) || 0,
                            startTop: parseFloat(box.dataset.top) || 0,
                            startWidth: parseFloat(box.dataset.width) || 1,
                            startHeight: parseFloat(box.dataset.height) || 1,
                            pointerId: e.pointerId,
                            isDragging: false
                        };
                        try { document.body.setPointerCapture(e.pointerId); } catch (_) {}
                        return;
                    }
                }

                // 3. 개체 (Box / Line) 클릭: 선택 및 다중 이동 드래그 준비
                const clickedObject = e.target.closest('.box, .line');
                if (clickedObject && e.button === 0) {
                    const isAlreadySelected = this.selectionManager.selectedElements.has(clickedObject);

                    // 미선택 개체 클릭 시 선택 반영
                    if (!isAlreadySelected) {
                        if (e.shiftKey) {
                            this.selectionManager.select(clickedObject, true);
                        } else {
                            this.selectionManager.select(clickedObject, false);
                        }
                    }

                    // 이동 대상 개체 목록 및 음수 좌표 이동 제한 계산
                    let minAllowedDeltaX = -Infinity;
                    let minAllowedDeltaY = -Infinity;
                    const items = [];

                    this.selectionManager.selectedElements.forEach(el => {
                        const left = parseFloat(el.dataset.left) || 0;
                        const top = parseFloat(el.dataset.top) || 0;
                        const width = parseFloat(el.dataset.width) || 0;
                        const height = parseFloat(el.dataset.height) || 0;

                        const minX = Math.min(left, left + width);
                        const minY = Math.min(top, top + height);

                        if (-minX > minAllowedDeltaX) minAllowedDeltaX = -minX;
                        if (-minY > minAllowedDeltaY) minAllowedDeltaY = -minY;

                        items.push({
                            el,
                            id: el.id,
                            type: el.classList.contains('box') ? 'box' : 'line',
                            initialLeft: left,
                            initialTop: top,
                            width,
                            height
                        });
                    });

                    // Box 이동 시 연결된 Line Endpoint 추적
                    const movingBoxes = items.filter(it => it.type === 'box');
                    const connectedLineEndpoints = [];
                    if (movingBoxes.length > 0) {
                        const movingLineIds = new Set(items.filter(it => it.type === 'line').map(it => it.id));

                        this.store.elementsMap.forEach(item => {
                            if (item.type === 'line' && !movingLineIds.has(item.id)) {
                                const lLeft = item.left;
                                const lTop = item.top;
                                const lWidth = item.width;
                                const lHeight = item.height;

                                const startPtX = lLeft;
                                const startPtY = lTop;
                                const endPtX = lLeft + lWidth;
                                const endPtY = lTop + lHeight;

                                let bindStart = false;
                                let bindEnd = false;

                                for (const b of movingBoxes) {
                                    const bLeft = b.initialLeft;
                                    const bTop = b.initialTop;
                                    const bRight = bLeft + b.width;
                                    const bBottom = bTop + b.height;

                                    if (startPtX >= bLeft && startPtX <= bRight && startPtY >= bTop && startPtY <= bBottom) {
                                        bindStart = true;
                                    }
                                    if (endPtX >= bLeft && endPtX <= bRight && endPtY >= bTop && endPtY <= bBottom) {
                                        bindEnd = true;
                                    }
                                }

                                if (bindStart || bindEnd) {
                                    connectedLineEndpoints.push({
                                        element: item.element,
                                        id: item.id,
                                        initialLeft: lLeft,
                                        initialTop: lTop,
                                        initialWidth: lWidth,
                                        initialHeight: lHeight,
                                        bindStart,
                                        bindEnd
                                    });
                                }
                            }
                        });

                        // 연결된 끝점이 음수 그리드 좌표로 나가지 않도록 이동 한계 제한
                        connectedLineEndpoints.forEach(conn => {
                            if (conn.bindStart) {
                                if (-conn.initialLeft > minAllowedDeltaX) minAllowedDeltaX = -conn.initialLeft;
                                if (-conn.initialTop > minAllowedDeltaY) minAllowedDeltaY = -conn.initialTop;
                            }
                            if (conn.bindEnd) {
                                const endX = conn.initialLeft + conn.initialWidth;
                                const endY = conn.initialTop + conn.initialHeight;
                                if (-endX > minAllowedDeltaX) minAllowedDeltaX = -endX;
                                if (-endY > minAllowedDeltaY) minAllowedDeltaY = -endY;
                            }
                        });
                    }

                    if (this.historyManager) this.historyManager.recordActionStart();

                    this.moveData = {
                        pointerId: e.pointerId,
                        startClientX: e.clientX,
                        startClientY: e.clientY,
                        minDeltaX: minAllowedDeltaX,
                        minDeltaY: minAllowedDeltaY,
                        items,
                        connectedLineEndpoints,
                        isDragging: false,
                        clickedObject,
                        isAlreadySelected,
                        isShift: e.shiftKey
                    };

                    // 클릭만 할 경우(편집 진입) 방해하지 않도록 setPointerCapture는 pointermove에서 드래그 시작 시에만 설정
                    return;
                }

                // 4. 빈 배경 클릭 (e.button === 0): 영역 선택(Marquee) 준비
                if (!this.addModeManager.currentMode && e.button === 0) {
                    const gridPos = this.viewport.screenToGridFloat(e.clientX, e.clientY);
                    this.marqueeData = {
                        pointerId: e.pointerId,
                        startX: gridPos.x,
                        startY: gridPos.y,
                        startClientX: e.clientX,
                        startClientY: e.clientY,
                        isDragging: false,
                        isShift: e.shiftKey,
                        initialSelection: new Set(this.selectionManager.selectedElements)
                    };
                    try { document.body.setPointerCapture(e.pointerId); } catch (_) {}
                }
            });

            // 포인터 이동
            document.addEventListener('pointermove', (e) => {
                // 터치 2손가락 제스처(핀치 줌 / 2손가락 패닝)
                if (e.pointerType === 'touch') {
                    this.activeTouches.set(e.pointerId, { clientX: e.clientX, clientY: e.clientY });
                    if (this.activeTouches.size === 2 && this.touchStartData) {
                        const data = this.getTouchMidpointAndDistance();
                        if (data && this.touchStartData.initialDist > 0) {
                            const scaleRatio = data.distance / this.touchStartData.initialDist;
                            const rawScale = Math.min(CONFIG.MAX_SCALE, Math.max(CONFIG.MIN_SCALE, this.touchStartData.initialScale * scaleRatio));
                            const newScale = getClosestZoomStep(rawScale);

                            const gridMidX = (this.touchStartData.initialMidX - this.touchStartData.initialPanX) / this.touchStartData.initialScale;
                            const gridMidY = (this.touchStartData.initialMidY - this.touchStartData.initialPanY) / this.touchStartData.initialScale;

                            const targetPanX = data.midX - gridMidX * newScale;
                            const targetPanY = data.midY - gridMidY * newScale;

                            const clamped = this.viewport.clampPan(targetPanX, targetPanY, newScale);
                            this.viewport.scale = newScale;
                            this.viewport.panX = clamped.x;
                            this.viewport.panY = clamped.y;
                            this.viewport.applyTransform();

                            const tooltipX = data.midX - 25;
                            const tooltipY = data.midY > 60 ? data.midY - 45 : data.midY + 45;
                            this.viewport.showTooltip(tooltipX, tooltipY, `${Math.round(newScale * 200)}%`, 1000);
                        }
                        return;
                    }
                }

                // 터치 롱프레스 이동 시 취소
                if (this.longPressTimer) {
                    const dist = Math.hypot(e.clientX - this.touchStartPos.x, e.clientY - this.touchStartPos.y);
                    if (dist > 8) {
                        clearTimeout(this.longPressTimer);
                        this.longPressTimer = null;
                    }
                }

                // 0. 박스 또는 선 드래그 생성 중
                if (this.drawInfo && this.drawInfo.pointerId === e.pointerId) {
                    const canvasX = (e.clientX - this.viewport.panX) / this.viewport.scale;
                    const canvasY = (e.clientY - this.viewport.panY) / this.viewport.scale;
                    const currCellX = Math.floor(canvasX / this.viewport.cellSize);
                    const currCellY = Math.floor(canvasY / this.viewport.cellSize);

                    if (this.drawInfo.type === 'box') {
                        const safeCurrX = Math.max(0, currCellX);
                        const safeCurrY = Math.max(0, currCellY);

                        const leftCell = Math.min(this.drawInfo.startCellX, safeCurrX);
                        const topCell = Math.min(this.drawInfo.startCellY, safeCurrY);
                        const widthCell = Math.max(1, Math.abs(safeCurrX - this.drawInfo.startCellX) + 1);
                        const heightCell = Math.max(1, Math.abs(safeCurrY - this.drawInfo.startCellY) + 1);

                        this.drawInfo.element.style.left = `${leftCell}em`;
                        this.drawInfo.element.style.top = `${topCell}em`;
                        this.drawInfo.element.style.width = `${widthCell}em`;
                        this.drawInfo.element.style.height = `${heightCell}em`;

                        this.drawInfo.element.dataset.left = leftCell;
                        this.drawInfo.element.dataset.top = topCell;
                        this.drawInfo.element.dataset.width = widthCell;
                        this.drawInfo.element.dataset.height = heightCell;

                        this.viewport.showTooltip(e.clientX + 14, e.clientY + 14, `W: ${widthCell}em, H: ${heightCell}em`, 0);
                        this.viewport.ensureGridSize(leftCell + widthCell, topCell + heightCell);
                        return;
                    } else if (this.drawInfo.type === 'line') {
                        const clampCurrX = Math.max(0, currCellX);
                        const clampCurrY = Math.max(0, currCellY);

                        const widthCell = clampCurrX - this.drawInfo.startCellX;
                        const heightCell = clampCurrY - this.drawInfo.startCellY;

                        this.drawInfo.element.dataset.left = this.drawInfo.startCellX;
                        this.drawInfo.element.dataset.top = this.drawInfo.startCellY;
                        this.drawInfo.element.dataset.width = widthCell;
                        this.drawInfo.element.dataset.height = heightCell;

                        this.store.updateLineVisual(this.drawInfo.element);
                        this.viewport.showTooltip(e.clientX + 14, e.clientY + 14, `W: ${Math.abs(widthCell)}em, H: ${Math.abs(heightCell)}em`, 0);
                        this.viewport.ensureGridSize(Math.max(this.drawInfo.startCellX, clampCurrX), Math.max(this.drawInfo.startCellY, clampCurrY));
                        return;
                    }
                }

                // A. 휠 클릭 패닝 중
                if (this.viewport.isPanning) {
                    const dx = e.clientX - this.viewport.panStartX;
                    const dy = e.clientY - this.viewport.panStartY;
                    this.viewport.setPan(this.viewport.startPanX + dx, this.viewport.startPanY + dy);
                    return;
                }

                // B. 리사이즈 (에지 또는 선 끝점) 드래그 중
                if (this.resizeData && this.resizeData.pointerId === e.pointerId) {
                    if (this.resizeData.type === 'line-point') {
                        if (!this.resizeData.isDragging) {
                            if (Math.hypot(e.clientX - this.resizeData.startClientX, e.clientY - this.resizeData.startClientY) > 2) {
                                this.resizeData.isDragging = true;
                            }
                        }

                        if (this.resizeData.isDragging) {
                            const dxPx = e.clientX - this.resizeData.startClientX;
                            const dyPx = e.clientY - this.resizeData.startClientY;

                            const deltaX = Math.round(dxPx / (this.viewport.scale * this.viewport.cellSize));
                            const deltaY = Math.round(dyPx / (this.viewport.scale * this.viewport.cellSize));

                            const line = this.resizeData.element;
                            const startL = this.resizeData.startLeft;
                            const startT = this.resizeData.startTop;
                            const startW = this.resizeData.startWidth;
                            const startH = this.resizeData.startHeight;

                            const targetX = this.resizeData.targetX;
                            const targetY = this.resizeData.targetY;
                            const newTargetX = Math.max(0, targetX + deltaX);
                            const newTargetY = Math.max(0, targetY + deltaY);

                            // 1. 주(Primary) Line 업데이트
                            let newL = startL;
                            let newT = startT;
                            let newW = startW;
                            let newH = startH;

                            if (this.resizeData.pointType === 'start') {
                                const fixedP2_x = startL + startW;
                                const fixedP2_y = startT + startH;
                                newL = newTargetX;
                                newT = newTargetY;
                                newW = fixedP2_x - newTargetX;
                                newH = fixedP2_y - newTargetY;
                            } else {
                                newL = startL;
                                newT = startT;
                                newW = newTargetX - startL;
                                newH = newTargetY - startT;
                            }

                            line.dataset.left = newL;
                            line.dataset.top = newT;
                            line.dataset.width = newW;
                            line.dataset.height = newH;

                            const data = this.store.elementsMap.get(line.id);
                            if (data) {
                                data.left = newL;
                                data.top = newT;
                                data.width = newW;
                                data.height = newH;
                            }

                            this.store.updateLineVisual(line);

                            let maxExpandX = Math.max(newL, newL + newW);
                            let maxExpandY = Math.max(newT, newT + newH);

                            // 2. 끝점을 공유하는 다른 Line들도 함께 업데이트 (Vertex Sharing)
                            if (this.resizeData.connectedPoints && this.resizeData.connectedPoints.length > 0) {
                                this.resizeData.connectedPoints.forEach(conn => {
                                    let cL = conn.startLeft;
                                    let cT = conn.startTop;
                                    let cW = conn.startWidth;
                                    let cH = conn.startHeight;

                                    if (conn.pointType === 'start') {
                                        const fixedP2_x = conn.startLeft + conn.startWidth;
                                        const fixedP2_y = conn.startTop + conn.startHeight;
                                        cL = newTargetX;
                                        cT = newTargetY;
                                        cW = fixedP2_x - newTargetX;
                                        cH = fixedP2_y - newTargetY;
                                    } else {
                                        cL = conn.startLeft;
                                        cT = conn.startTop;
                                        cW = newTargetX - conn.startLeft;
                                        cH = newTargetY - conn.startTop;
                                    }

                                    conn.element.dataset.left = cL;
                                    conn.element.dataset.top = cT;
                                    conn.element.dataset.width = cW;
                                    conn.element.dataset.height = cH;

                                    const cData = this.store.elementsMap.get(conn.id);
                                    if (cData) {
                                        cData.left = cL;
                                        cData.top = cT;
                                        cData.width = cW;
                                        cData.height = cH;
                                    }

                                    this.store.updateLineVisual(conn.element);

                                    const connMaxX = Math.max(cL, cL + cW);
                                    const connMaxY = Math.max(cT, cT + cH);
                                    if (connMaxX > maxExpandX) maxExpandX = connMaxX;
                                    if (connMaxY > maxExpandY) maxExpandY = connMaxY;
                                });
                            }

                            this.viewport.showTooltip(e.clientX + 14, e.clientY + 14, `W: ${Math.abs(newW)}em, H: ${Math.abs(newH)}em`, 0);
                            this.viewport.ensureGridSize(maxExpandX, maxExpandY);
                            return;
                        }
                    } else {
                        // box-edge 리사이즈
                        if (!this.resizeData.isDragging) {
                            if (Math.hypot(e.clientX - this.resizeData.startClientX, e.clientY - this.resizeData.startClientY) > 2) {
                                this.resizeData.isDragging = true;
                                if (this.resizeData.edge === 'top' || this.resizeData.edge === 'bottom') {
                                    document.body.classList.add('is-resizing-ns');
                                } else {
                                    document.body.classList.add('is-resizing-ew');
                                }
                            }
                        }

                        if (this.resizeData.isDragging) {
                            const dxPx = e.clientX - this.resizeData.startClientX;
                            const dyPx = e.clientY - this.resizeData.startClientY;

                            const deltaX = Math.round(dxPx / (this.viewport.scale * this.viewport.cellSize));
                            const deltaY = Math.round(dyPx / (this.viewport.scale * this.viewport.cellSize));

                            const { box, edge, startLeft, startTop, startWidth, startHeight } = this.resizeData;
                            let newL = startLeft;
                            let newT = startTop;
                            let newW = startWidth;
                            let newH = startHeight;

                            if (edge === 'right') {
                                newW = Math.max(1, startWidth + deltaX);
                            } else if (edge === 'bottom') {
                                newH = Math.max(1, startHeight + deltaY);
                            } else if (edge === 'left') {
                                newL = Math.max(0, Math.min(startLeft + startWidth - 1, startLeft + deltaX));
                                newW = startLeft + startWidth - newL;
                            } else if (edge === 'top') {
                                newT = Math.max(0, Math.min(startTop + startHeight - 1, startTop + deltaY));
                                newH = startTop + startHeight - newT;
                            }

                            box.dataset.left = newL;
                            box.dataset.top = newT;
                            box.dataset.width = newW;
                            box.dataset.height = newH;

                            box.style.left = `${newL}em`;
                            box.style.top = `${newT}em`;
                            box.style.width = `${newW}em`;
                            box.style.height = `${newH}em`;

                            const item = this.store.elementsMap.get(box.id);
                            if (item) {
                                item.left = newL;
                                item.top = newT;
                                item.width = newW;
                                item.height = newH;
                            }

                            this.viewport.showTooltip(e.clientX + 14, e.clientY + 14, `W: ${newW}em, H: ${newH}em`, 0);
                            this.viewport.ensureGridSize(newL + newW, newT + newH);
                            return;
                        }
                    }
                }

                // C. 선택된 개체 다중 이동 드래그 중
                if (this.moveData && this.moveData.pointerId === e.pointerId) {
                    if (!this.moveData.isDragging) {
                        if (Math.hypot(e.clientX - this.moveData.startClientX, e.clientY - this.moveData.startClientY) > 3) {
                            this.moveData.isDragging = true;
                            document.body.classList.add('is-moving-objects');
                            try { document.body.setPointerCapture(e.pointerId); } catch (_) {}
                        }
                    }

                    if (this.moveData.isDragging) {
                        const dxPx = e.clientX - this.moveData.startClientX;
                        const dyPx = e.clientY - this.moveData.startClientY;

                        const rawDeltaX = Math.round(dxPx / (this.viewport.scale * this.viewport.cellSize));
                        const rawDeltaY = Math.round(dyPx / (this.viewport.scale * this.viewport.cellSize));

                        const deltaX = Math.max(this.moveData.minDeltaX, rawDeltaX);
                        const deltaY = Math.max(this.moveData.minDeltaY, rawDeltaY);

                        let minOverallX = Infinity;
                        let minOverallY = Infinity;
                        let maxOverallRight = 0;
                        let maxOverallBottom = 0;

                        this.moveData.items.forEach(it => {
                            const newLeft = it.initialLeft + deltaX;
                            const newTop = it.initialTop + deltaY;

                            it.el.dataset.left = newLeft;
                            it.el.dataset.top = newTop;
                            it.el.style.left = `${newLeft}em`;
                            it.el.style.top = `${newTop}em`;

                            const item = this.store.elementsMap.get(it.id);
                            if (item) {
                                item.left = newLeft;
                                item.top = newTop;
                                if (item.type === 'line') {
                                    this.store.updateLineVisual(it.el);
                                }
                            }

                            if (item && item.type === 'line') {
                                const w = it.width || 0;
                                const h = it.height || 0;
                                const itemMinX = Math.min(newLeft, newLeft + w);
                                const itemMinY = Math.min(newTop, newTop + h);
                                if (itemMinX < minOverallX) minOverallX = itemMinX;
                                if (itemMinY < minOverallY) minOverallY = itemMinY;
                                const right = Math.max(newLeft, newLeft + w);
                                const bottom = Math.max(newTop, newTop + h);
                                if (right > maxOverallRight) maxOverallRight = right;
                                if (bottom > maxOverallBottom) maxOverallBottom = bottom;
                            } else {
                                if (newLeft < minOverallX) minOverallX = newLeft;
                                if (newTop < minOverallY) minOverallY = newTop;
                                const right = newLeft + it.width;
                                const bottom = newTop + it.height;
                                if (right > maxOverallRight) maxOverallRight = right;
                                if (bottom > maxOverallBottom) maxOverallBottom = bottom;
                            }
                        });

                        // Box 이동에 따라 연결된 Line의 끝점 함께 이동 및 갱신
                        if (this.moveData.connectedLineEndpoints && this.moveData.connectedLineEndpoints.length > 0) {
                            this.moveData.connectedLineEndpoints.forEach(conn => {
                                const initStartX = conn.initialLeft;
                                const initStartY = conn.initialTop;
                                const initEndX = conn.initialLeft + conn.initialWidth;
                                const initEndY = conn.initialTop + conn.initialHeight;

                                const curStartX = conn.bindStart ? (initStartX + deltaX) : initStartX;
                                const curStartY = conn.bindStart ? (initStartY + deltaY) : initStartY;
                                const curEndX = conn.bindEnd ? (initEndX + deltaX) : initEndX;
                                const curEndY = conn.bindEnd ? (initEndY + deltaY) : initEndY;

                                const newL = curStartX;
                                const newT = curStartY;
                                const newW = curEndX - curStartX;
                                const newH = curEndY - curStartY;

                                conn.element.dataset.left = newL;
                                conn.element.dataset.top = newT;
                                conn.element.dataset.width = newW;
                                conn.element.dataset.height = newH;

                                const data = this.store.elementsMap.get(conn.id);
                                if (data) {
                                    data.left = newL;
                                    data.top = newT;
                                    data.width = newW;
                                    data.height = newH;
                                }

                                this.store.updateLineVisual(conn.element);

                                const right = Math.max(newL, newL + newW);
                                const bottom = Math.max(newT, newT + newH);
                                if (right > maxOverallRight) maxOverallRight = right;
                                if (bottom > maxOverallBottom) maxOverallBottom = bottom;
                            });
                        }

                        if (minOverallX !== Infinity && minOverallY !== Infinity) {
                            this.viewport.showTooltip(e.clientX + 14, e.clientY + 14, `X: ${minOverallX}em, Y: ${minOverallY}em`, 0);
                        }

                        this.viewport.ensureGridSize(maxOverallRight, maxOverallBottom);
                        return;
                    }
                }

                // D. 영역 선택(Marquee) 사각형 드래그 중
                if (this.marqueeData && this.marqueeData.pointerId === e.pointerId) {
                    if (!this.marqueeData.isDragging) {
                        if (Math.hypot(e.clientX - this.marqueeData.startClientX, e.clientY - this.marqueeData.startClientY) > 4) {
                            this.marqueeData.isDragging = true;
                        }
                    }

                    if (this.marqueeData.isDragging && this.marqueeEl) {
                        const currPos = this.viewport.screenToGridFloat(e.clientX, e.clientY);
                        const mLeft = Math.min(this.marqueeData.startX, currPos.x);
                        const mRight = Math.max(this.marqueeData.startX, currPos.x);
                        const mTop = Math.min(this.marqueeData.startY, currPos.y);
                        const mBottom = Math.max(this.marqueeData.startY, currPos.y);

                        this.marqueeEl.style.left = `${mLeft}em`;
                        this.marqueeEl.style.top = `${mTop}em`;
                        this.marqueeEl.style.width = `${mRight - mLeft}em`;
                        this.marqueeEl.style.height = `${mBottom - mTop}em`;
                        this.marqueeEl.style.display = 'block';
                    }
                }
            });

            // 포인터 업: 동작 완료 처리
            const endAction = (e) => {
                // 0. 박스 또는 선 드래그 생성 완료 처리
                if (this.drawInfo && this.drawInfo.pointerId === e.pointerId) {
                    try { document.body.releasePointerCapture(e.pointerId); } catch (_) {}
                    this.viewport.hideTooltip();

                    const createdElement = this.drawInfo.element;
                    const drawType = this.drawInfo.type;
                    this.drawInfo = null;

                    if (e.type === 'pointercancel') {
                        if (createdElement) createdElement.remove();
                        if (this.historyManager) this.historyManager.discardActionStart();
                        this.addModeManager.setMode(null);
                        return;
                    }

                    if (createdElement) {
                        if (drawType === 'box') {
                            const left = parseInt(createdElement.dataset.left) || 0;
                            const top = parseInt(createdElement.dataset.top) || 0;
                            const width = parseInt(createdElement.dataset.width) || 1;
                            const height = parseInt(createdElement.dataset.height) || 1;

                            this.store.registerBoxElement(createdElement, left, top, width, height, '');
                            this.selectionManager.select(createdElement);
                            if (this.historyManager) this.historyManager.commitAction();
                            this.textEditor.startEditing(createdElement);
                        } else if (drawType === 'line') {
                            const w = parseInt(createdElement.dataset.width) || 0;
                            const h = parseInt(createdElement.dataset.height) || 0;
                            if (w === 0 && h === 0) {
                                createdElement.remove();
                                if (this.historyManager) this.historyManager.discardActionStart();
                            } else {
                                const left = parseInt(createdElement.dataset.left) || 0;
                                const top = parseInt(createdElement.dataset.top) || 0;
                                this.store.registerLineElement(createdElement, left, top, w, h);
                                this.selectionManager.select(createdElement);
                                if (this.historyManager) this.historyManager.commitAction();
                            }
                        }
                    } else {
                        if (this.historyManager) this.historyManager.discardActionStart();
                    }

                    this.addModeManager.setMode(null);
                    return;
                }

                // A. 패닝 종료
                if (this.viewport.isPanning) {
                    this.viewport.isPanning = false;
                    document.body.classList.remove('is-panning');
                    try { document.body.releasePointerCapture(e.pointerId); } catch (_) {}
                    this.store.queueRenderVisibleBoxes(50);
                }

                // B. 에지/선 끝점 리사이즈 종료
                if (this.resizeData && this.resizeData.pointerId === e.pointerId) {
                    try { document.body.releasePointerCapture(e.pointerId); } catch (_) {}
                    document.body.classList.remove('is-resizing-ns', 'is-resizing-ew');
                    this.viewport.hideTooltip();
                    if (this.resizeData.isDragging) {
                        if (this.historyManager) this.historyManager.commitAction();
                    } else {
                        if (this.historyManager) this.historyManager.discardActionStart();
                    }
                    this.resizeData = null;
                }

                // C. 개체 이동 종료
                if (this.moveData && this.moveData.pointerId === e.pointerId) {
                    if (this.moveData.isDragging) {
                        try { document.body.releasePointerCapture(e.pointerId); } catch (_) {}
                        document.body.classList.remove('is-moving-objects');
                        this.viewport.hideTooltip();
                        if (this.historyManager) this.historyManager.commitAction();
                    } else {
                        if (this.historyManager) this.historyManager.discardActionStart();
                        // 드래그하지 않고 단순 클릭한 경우의 처리
                        if (this.moveData.isShift && this.moveData.isAlreadySelected) {
                            this.selectionManager.select(this.moveData.clickedObject, true);
                        } else if (!this.moveData.isShift && this.selectionManager.selectedElements.size > 1) {
                            this.selectionManager.select(this.moveData.clickedObject, false);
                        } else if (!this.moveData.isShift && this.moveData.isAlreadySelected && this.moveData.clickedObject.classList.contains('box')) {
                            // 이미 선택된 상태의 박스를 단순 클릭 -> 텍스트 편집 모드 진입 및 클릭 위치에 커서 배치
                            this.textEditor.startEditing(this.moveData.clickedObject, e.clientX, e.clientY);
                        }
                    }

                    this.moveData = null;
                }

                // D. 영역 선택(Marquee) 종료 및 박스 접촉 개체 판정
                if (this.marqueeData && this.marqueeData.pointerId === e.pointerId) {
                    try { document.body.releasePointerCapture(e.pointerId); } catch (_) {}

                    if (this.marqueeData.isDragging) {
                        const currPos = this.viewport.screenToGridFloat(e.clientX, e.clientY);
                        const mLeft = Math.min(this.marqueeData.startX, currPos.x);
                        const mRight = Math.max(this.marqueeData.startX, currPos.x);
                        const mTop = Math.min(this.marqueeData.startY, currPos.y);
                        const mBottom = Math.max(this.marqueeData.startY, currPos.y);

                        // 드롭 영역과 접촉/교차하는 모든 개체 선택
                        const newSelection = new Set(this.marqueeData.isShift ? this.marqueeData.initialSelection : []);
                        this.store.elementsMap.forEach(item => {
                            if (item.type === 'box') {
                                if (isBoxItemIntersecting(item, mLeft, mTop, mRight, mBottom)) {
                                    newSelection.add(item.element);
                                }
                            } else if (item.type === 'line') {
                                if (isLineItemIntersecting(item, mLeft, mTop, mRight, mBottom)) {
                                    newSelection.add(item.element);
                                }
                            }
                        });

                        this.selectionManager.setSelection(newSelection);
                        if (this.marqueeEl) this.marqueeEl.style.display = 'none';
                    } else {
                        // 드래그 없이 빈 공간 단순 클릭 -> 선택 해제 (Shift 미입력 시)
                        if (!this.marqueeData.isShift) {
                            this.selectionManager.clear();
                        }
                    }

                    this.marqueeData = null;
                }

                if (e.pointerType === 'touch') {
                    this.activeTouches.delete(e.pointerId);
                    if (this.activeTouches.size < 2) {
                        if (this.touchStartData) {
                            this.store.queueRenderVisibleBoxes(50);
                        }
                        this.touchStartData = null;
                    }
                }

                if (this.longPressTimer) {
                    clearTimeout(this.longPressTimer);
                    this.longPressTimer = null;
                }
            };

            document.addEventListener('pointerup', endAction);
            document.addEventListener('pointercancel', endAction);

            // 마우스 휠 줌/스크롤 시 뷰포트 영역 내 미렌더링 박스 지연 렌더링
            window.addEventListener('wheel', () => {
                this.store.queueRenderVisibleBoxes(120);
            }, { passive: true });

            // 단축키 핸들러
            window.addEventListener('keydown', (e) => {
                const isEditing = Boolean(this.textEditor.activeBox);

                if (isEditing) {
                    if (e.key === 'Escape') {
                        e.preventDefault();
                        e.stopPropagation();
                        this.textEditor.stopEditing();
                    }
                    return;
                }

                // 실행 취소 / 다시 실행 (Undo / Redo)
                if ((e.ctrlKey || e.metaKey) && !e.altKey) {
                    const key = e.key.toLowerCase();
                    if (key === 'z') {
                        e.preventDefault();
                        if (e.shiftKey) {
                            if (this.historyManager) this.historyManager.redo();
                        } else {
                            if (this.historyManager) this.historyManager.undo();
                        }
                        return;
                    } else if (key === 'y') {
                        e.preventDefault();
                        if (this.historyManager) this.historyManager.redo();
                        return;
                    }
                }

                // Ctrl+S: GitHub 연동 시 즉시 GitHub 커밋 저장, 미연동 시 data.json 파일 다운로드
                // Ctrl+O: data.json 파일 가져오기 (열기)
                if ((e.ctrlKey || e.metaKey) && !e.altKey) {
                    const key = e.key.toLowerCase();
                    if (key === 's') {
                        e.preventDefault();
                        if (this.dataManager) {
                            if (this.dataManager.getGitHubConfig()) {
                                if (this.dataManager.saveTimer) {
                                    clearTimeout(this.dataManager.saveTimer);
                                }
                                this.dataManager.executeSave();
                            } else {
                                this.dataManager.exportJsonFile();
                            }
                        }
                        return;
                    } else if (key === 'o') {
                        e.preventDefault();
                        if (this.dataManager) this.dataManager.importJsonFile();
                        return;
                    }
                }

                // Escape: 모달 닫기, 컨텍스트 메뉴 닫기 또는 선택 해제
                if (e.key === 'Escape') {
                    const modal = document.getElementById('cloud-settings-modal');
                    if (modal && modal.classList.contains('show')) {
                        modal.classList.remove('show');
                        return;
                    }
                    if (this.contextMenuEl && this.contextMenuEl.classList.contains('show')) {
                        this.hideContextMenu();
                        return;
                    }
                    if (this.addModeManager.currentMode) {
                        this.addModeManager.setMode(null);
                    } else {
                        this.selectionManager.clear();
                    }
                    return;
                }

                // Enter: 선택된 단일 박스 글쓰기(편집) 모드 진입
                if (e.key === 'Enter') {
                    if (this.selectionManager.selectedElements.size === 1) {
                        const [selectedBox] = this.selectionManager.selectedElements;
                        if (selectedBox && selectedBox.classList.contains('box')) {
                            e.preventDefault();
                            this.textEditor.startEditing(selectedBox);
                        }
                    }
                    return;
                }

                // Delete: 선택된 모든 개체 삭제
                if (e.key === 'Delete') {
                    if (this.selectionManager.selectedElements.size > 0) {
                        e.preventDefault();
                        this.selectionManager.deleteSelected(this.store, this.historyManager);
                    }
                    return;
                }
            });

            // 상단 삭제 버튼 클릭
            const deleteBtn = document.getElementById('delete-btn');
            if (deleteBtn) {
                deleteBtn.addEventListener('click', (e) => {
                    e.stopPropagation();
                    this.selectionManager.deleteSelected(this.store, this.historyManager);
                });
            }
        }
    }

    // =========================================================================
    // 9. 데이터 관리자 (GitHub REST API & Local Data Manager)
    // =========================================================================
    // 9. 데이터 관리자 (GitHub REST API & data.json Data Manager)
    //    - GitHub REST API data.json 실시간 fetch 및 10초 주기 자동 커밋
    //    - data.json 직접 내보내기/가져오기 (Export/Import)
    // =========================================================================
    class DataManager {
        constructor(store, viewport) {
            this.store = store;
            this.viewport = viewport;
            this.saveTimer = null;
            this.isSaving = false;
            this.fileSha = null;
            this.lastSavedJson = null;
            this.isDirty = false;
        }

        clearIndexedDB() {
            try {
                if (window.indexedDB) {
                    indexedDB.deleteDatabase('note-app-db');
                    console.log('[DataManager] IndexedDB 로컬 캐시 삭제 완료');
                }
            } catch (e) {
                console.warn('[DataManager] IndexedDB 삭제 오류:', e);
            }
        }

        getGitHubConfig() {
            try {
                const localSaved = localStorage.getItem('note_github_config');
                if (localSaved) {
                    const parsed = JSON.parse(localSaved);
                    if (parsed && parsed.owner && parsed.repo && parsed.token) {
                        return parsed;
                    }
                }
            } catch (_) {}

            if (window.GITHUB_CONFIG && window.GITHUB_CONFIG.owner && window.GITHUB_CONFIG.repo && window.GITHUB_CONFIG.token) {
                return window.GITHUB_CONFIG;
            }

            return null;
        }

        utf8ToBase64(str) {
            return btoa(encodeURIComponent(str).replace(/%([0-9A-F]{2})/g, (_, p1) => String.fromCharCode('0x' + p1)));
        }

        base64ToUtf8(str) {
            const cleanStr = (str || '').replace(/\s+/g, '');
            return decodeURIComponent(Array.prototype.map.call(atob(cleanStr), c => '%' + ('00' + c.charCodeAt(0).toString(16)).slice(-2)).join(''));
        }

        updateCloudStatus(state, text) {
            const badge = document.getElementById('cloud-status-indicator');
            if (!badge) return;
            const dot = badge.querySelector('.status-dot');
            const label = badge.querySelector('.status-text');

            if (dot) {
                dot.className = `status-dot ${state}`;
            }
            if (label) {
                label.textContent = text;
            }
            badge.title = `동기화 상태: ${text} (클릭하여 GitHub 설정)`;
        }

        getSerializedData() {
            const data = {
                objects: [],
                lines: []
            };

            const boxes = [];
            const lines = [];

            this.store.elementsMap.forEach(item => {
                if (item.type === 'box') boxes.push(item);
                else if (item.type === 'line') lines.push(item);
            });

            // 위쪽 -> 왼쪽 순서로 정렬하여 일관성 유지
            boxes.sort((a, b) => (a.top - b.top) || (a.left - b.left));
            lines.sort((a, b) => (a.top - b.top) || (a.left - b.left));

            boxes.forEach(box => {
                data.objects.push({
                    id: box.id,
                    left: box.left,
                    top: box.top,
                    width: box.width,
                    height: box.height,
                    contents: box.text || ''
                });
            });

            lines.forEach(line => {
                data.lines.push({
                    id: line.id,
                    left: line.left,
                    top: line.top,
                    width: line.width,
                    height: line.height
                });
            });

            return data;
        }

        renderData(data) {
            if (!data) return;

            // 기존 캔버스 요소 정리
            const existingIds = Array.from(this.store.elementsMap.keys());
            existingIds.forEach(id => this.store.removeElement(id));

            const objects = data.objects || [];
            objects.forEach(obj => {
                const isLine = (obj.id && obj.id.startsWith('l')) || obj.contents === undefined;
                const left = parseInt(obj.left) || 0;
                const top = parseInt(obj.top) || 0;

                if (isLine) {
                    const width = parseInt(obj.width) || 0;
                    const height = parseInt(obj.height) || 0;
                    this.store.createLineElement(obj.id, left, top, width, height);
                } else {
                    const width = parseInt(obj.width) || CONFIG.DEFAULT_BOX_WIDTH_EM;
                    const height = parseInt(obj.height) || CONFIG.DEFAULT_BOX_HEIGHT_EM;
                    const contents = (obj.contents || '').replace(/&nbsp;/g, ' ').replace(/\u00a0/g, ' ');
                    this.store.createBoxElement(obj.id, left, top, width, height, contents, true);
                }
            });

            const lines = data.lines || [];
            lines.forEach(line => {
                const left = parseInt(line.left) || 0;
                const top = parseInt(line.top) || 0;
                const width = parseInt(line.width) || 0;
                const height = parseInt(line.height) || 0;
                this.store.createLineElement(line.id, left, top, width, height);
            });

            // 현재 화면 중심 영역에 있는 박스들 우선 렌더링
            this.store.renderVisibleBoxes();

            // 초기 로드 시점의 데이터 스냅샷 저장 및 dirty 플래그 초기화
            this.lastSavedJson = JSON.stringify(this.getSerializedData());
            this.isDirty = false;
        }

        async fetchDefaultData() {
            try {
                const resp = await fetch(`data.json?_t=${Date.now()}`);
                if (resp.ok) {
                    return await resp.json();
                }
            } catch (err) {
                console.log('[DataManager] data.json fetch 불가 (로컬 오프라인 등):', err.message);
            }
            return { objects: [], lines: [] };
        }

        async loadInitialData() {
            // 브라우저에 남아있던 이전 IndexedDB 캐시 완전히 제거
            this.clearIndexedDB();

            const config = this.getGitHubConfig();

            if (config) {
                try {
                    this.updateCloudStatus('syncing', 'GitHub 데이터 로드 중...');
                    const path = encodeURIComponent(config.path || 'data.json').replace(/%2F/g, '/');
                    const branch = config.branch || 'main';
                    const apiUrl = `https://api.github.com/repos/${config.owner}/${config.repo}/contents/${path}?ref=${branch}&_t=${Date.now()}`;

                    const res = await fetch(apiUrl, {
                        headers: {
                            'Authorization': `Bearer ${config.token}`,
                            'Accept': 'application/vnd.github.v3+json'
                        }
                    });

                    if (res.ok) {
                        const fileInfo = await res.json();
                        this.fileSha = fileInfo.sha;
                        if (fileInfo.content) {
                            const jsonText = this.base64ToUtf8(fileInfo.content);
                            const parsedData = JSON.parse(jsonText);
                            this.renderData(parsedData);
                            this.updateCloudStatus('synced', 'GitHub 동기화됨');
                            console.log('[DataManager] GitHub data.json 로드 완료, SHA:', this.fileSha);
                            return;
                        }
                    } else if (res.status === 404) {
                        console.log('[DataManager] GitHub 저장소에 data.json 없음 (404), 기본 data.json 로드');
                    } else {
                        throw new Error(`GitHub API 오류 (${res.status} ${res.statusText})`);
                    }
                } catch (err) {
                    console.warn('[DataManager] GitHub 데이터 로드 실패, 기본 data.json 로드:', err.message);
                    this.updateCloudStatus('error', 'GitHub 연결 실패');
                }
            }

            // GitHub 미연동 또는 실패 시 기본 data.json 로드
            const defaultData = (await this.fetchDefaultData()) || { objects: [], lines: [] };
            this.renderData(defaultData);
            this.updateCloudStatus('offline', '로컬 모드 (GitHub 미연동)');
        }

        queueAutoSave(delay = 10000) {
            if (this.saveTimer) clearTimeout(this.saveTimer);

            // 실제 내용 변경 여부 검증 (수정사항이 없으면 타이머 가동 안 함)
            const currentData = this.getSerializedData();
            const currentJson = JSON.stringify(currentData);
            if (this.lastSavedJson && this.lastSavedJson === currentJson) {
                this.isDirty = false;
                return;
            }
            this.isDirty = true;

            const config = this.getGitHubConfig();
            if (config) {
                this.updateCloudStatus('syncing', '10초 후 GitHub 저장...');
                this.saveTimer = setTimeout(async () => {
                    await this.executeSave();
                }, delay);
            } else {
                this.updateCloudStatus('offline', '로컬 모드 (GitHub 미연동)');
            }
        }

        async executeSave() {
            if (this.isSaving) return;

            // 저장 직전 다시 한번 변경사항 검증
            const currentData = this.getSerializedData();
            const currentJson = JSON.stringify(currentData);
            if (this.lastSavedJson && this.lastSavedJson === currentJson) {
                this.isDirty = false;
                return;
            }

            this.isSaving = true;

            try {
                const config = this.getGitHubConfig();
                if (!config) {
                    this.updateCloudStatus('offline', '로컬 모드 (GitHub 미연동)');
                    return;
                }

                this.updateCloudStatus('syncing', 'GitHub에 저장 중...');

                const path = encodeURIComponent(config.path || 'data.json').replace(/%2F/g, '/');
                const branch = config.branch || 'main';
                const apiUrl = `https://api.github.com/repos/${config.owner}/${config.repo}/contents/${path}`;

                // SHA가 없으면 커밋 전에 현재 원격 파일의 SHA를 조회하여 충돌 방지
                if (!this.fileSha) {
                    try {
                        const checkRes = await fetch(`${apiUrl}?ref=${branch}&_t=${Date.now()}`, {
                            headers: {
                                'Authorization': `Bearer ${config.token}`,
                                'Accept': 'application/vnd.github.v3+json'
                            }
                        });
                        if (checkRes.ok) {
                            const fileInfo = await checkRes.json();
                            this.fileSha = fileInfo.sha;
                        }
                    } catch (_) {}
                }

                const jsonStr = JSON.stringify(currentData, null, 2);
                const base64Content = this.utf8ToBase64(jsonStr);

                const payload = {
                    message: `Auto-save note data [${new Date().toLocaleTimeString('ko-KR')}]`,
                    content: base64Content,
                    branch: branch
                };
                if (this.fileSha) {
                    payload.sha = this.fileSha;
                }

                const putRes = await fetch(apiUrl, {
                    method: 'PUT',
                    headers: {
                        'Authorization': `Bearer ${config.token}`,
                        'Accept': 'application/vnd.github.v3+json',
                        'Content-Type': 'application/json'
                    },
                    body: JSON.stringify(payload)
                });

                if (putRes.ok) {
                    const resJson = await putRes.json();
                    this.fileSha = resJson.content?.sha || resJson.commit?.sha || this.fileSha;
                    this.lastSavedJson = currentJson;
                    this.isDirty = false;
                    const now = new Date();
                    const timeStr = `${String(now.getHours()).padStart(2, '0')}:${String(now.getMinutes()).padStart(2, '0')}:${String(now.getSeconds()).padStart(2, '0')}`;
                    this.updateCloudStatus('synced', `GitHub 저장됨 (${timeStr})`);
                    console.log('[DataManager] GitHub REST API 자동 커밋 완료 (10초 주기), SHA:', this.fileSha);
                } else {
                    const errData = await putRes.json().catch(() => ({}));
                    if (putRes.status === 409) {
                        this.fileSha = null; // 다음 시도 시 최신 SHA 재조회
                    }
                    throw new Error(errData.message || `HTTP ${putRes.status}`);
                }
            } catch (err) {
                console.error('[DataManager] GitHub 자동 저장 실패:', err);
                this.updateCloudStatus('error', `저장 오류 (${err.message})`);
            } finally {
                this.isSaving = false;
            }
        }

        exportJsonFile() {
            const data = this.getSerializedData();
            const jsonStr = JSON.stringify(data, null, 2);
            const blob = new Blob([jsonStr], { type: 'application/json' });
            const url = URL.createObjectURL(blob);
            const a = document.createElement('a');
            a.href = url;
            a.download = 'data.json';
            document.body.appendChild(a);
            a.click();
            document.body.removeChild(a);
            URL.revokeObjectURL(url);
        }

        importJsonFile() {
            const fileInput = document.getElementById('file-input');
            if (fileInput) fileInput.click();
        }

        bindFileInput() {
            const fileInput = document.getElementById('file-input');
            if (fileInput) {
                fileInput.addEventListener('change', (e) => {
                    const file = e.target.files?.[0];
                    if (!file) return;
                    const reader = new FileReader();
                    reader.onload = async (evt) => {
                        try {
                            const data = JSON.parse(evt.target.result);
                            this.renderData(data);
                            this.queueAutoSave(100);
                            console.log('[DataManager] JSON 파일 불러오기 성공');
                        } catch (err) {
                            alert('올바른 JSON 형식이 아닙니다: ' + err.message);
                        }
                    };
                    reader.readAsText(file);
                    fileInput.value = ''; // 재선택 가능하도록 초기화
                });
            }
        }

        bindCloudModal() {
            const badge = document.getElementById('cloud-status-indicator');
            const modal = document.getElementById('cloud-settings-modal');
            const closeBtn = document.getElementById('modal-close-btn');
            const cancelBtn = document.getElementById('modal-cancel-btn');
            const saveBtn = document.getElementById('modal-save-btn');
            const resetBtn = document.getElementById('modal-reset-btn');
            const repoInput = document.getElementById('github-repo-input');
            const pathInput = document.getElementById('github-path-input');
            const branchInput = document.getElementById('github-branch-input');
            const tokenInput = document.getElementById('github-token-input');
            const statusMsg = document.getElementById('modal-status-msg');

            const openModal = () => {
                if (!modal) return;
                const currentConfig = this.getGitHubConfig();
                if (currentConfig) {
                    if (repoInput) repoInput.value = (currentConfig.owner && currentConfig.repo) ? `${currentConfig.owner}/${currentConfig.repo}` : '';
                    if (pathInput) pathInput.value = currentConfig.path || 'data.json';
                    if (branchInput) branchInput.value = currentConfig.branch || 'main';
                    if (tokenInput) tokenInput.value = currentConfig.token || '';
                }
                if (statusMsg) {
                    statusMsg.textContent = '';
                    statusMsg.className = 'modal-status-msg';
                }
                modal.classList.add('show');
            };

            const closeModal = () => {
                if (modal) modal.classList.remove('show');
            };

            if (badge) badge.addEventListener('click', openModal);
            if (closeBtn) closeBtn.addEventListener('click', closeModal);
            if (cancelBtn) cancelBtn.addEventListener('click', closeModal);
            if (modal) {
                modal.addEventListener('click', (e) => {
                    if (e.target === modal) closeModal();
                });
            }

            if (resetBtn) {
                resetBtn.addEventListener('click', () => {
                    if (confirm('GitHub 연동 설정을 초기화하고 로컬 모드로 전환하시겠습니까?')) {
                        localStorage.removeItem('note_github_config');
                        if (repoInput) repoInput.value = '';
                        if (tokenInput) tokenInput.value = '';
                        this.fileSha = null;
                        this.updateCloudStatus('offline', '로컬 모드 (GitHub 미연동)');
                        if (statusMsg) {
                            statusMsg.textContent = '연동 설정이 초기화되었습니다.';
                            statusMsg.className = 'modal-status-msg success';
                        }
                    }
                });
            }

            if (saveBtn) {
                saveBtn.addEventListener('click', async () => {
                    const rawRepo = (repoInput?.value || '').trim();
                    const path = (pathInput?.value || 'data.json').trim();
                    const branch = (branchInput?.value || 'main').trim();
                    const token = (tokenInput?.value || '').trim();

                    if (!rawRepo || !token) {
                        if (statusMsg) {
                            statusMsg.textContent = '저장소(owner/repo)와 GitHub Token을 모두 입력해 주세요.';
                            statusMsg.className = 'modal-status-msg error';
                        }
                        return;
                    }

                    const parts = rawRepo.split('/').map(s => s.trim()).filter(Boolean);
                    if (parts.length < 2) {
                        if (statusMsg) {
                            statusMsg.textContent = "저장소 형식을 '아이디/저장소이름' 형식으로 입력해 주세요. (예: octocat/my-notes)";
                            statusMsg.className = 'modal-status-msg error';
                        }
                        return;
                    }

                    const owner = parts[0];
                    const repo = parts[1];

                    if (statusMsg) {
                        statusMsg.textContent = 'GitHub 저장소 연결 테스트 중...';
                        statusMsg.className = 'modal-status-msg';
                    }

                    try {
                        // 저장소 접근 권한 테스트
                        const testUrl = `https://api.github.com/repos/${owner}/${repo}`;
                        const testRes = await fetch(testUrl, {
                            headers: {
                                'Authorization': `Bearer ${token}`,
                                'Accept': 'application/vnd.github.v3+json'
                            }
                        });

                        if (!testRes.ok) {
                            if (testRes.status === 401) throw new Error('유효하지 않은 Token(토큰)입니다.');
                            if (testRes.status === 404) throw new Error('저장소를 찾을 수 없습니다. 아이디와 저장소명을 확인하세요.');
                            throw new Error(`GitHub 오류 (${testRes.status})`);
                        }

                        const newConfig = { owner, repo, path, branch, token };
                        localStorage.setItem('note_github_config', JSON.stringify(newConfig));
                        this.fileSha = null;

                        if (statusMsg) {
                            statusMsg.textContent = 'GitHub 연결 성공! 최신 data.json을 불러오는 중...';
                            statusMsg.className = 'modal-status-msg success';
                        }

                        await this.loadInitialData();

                        setTimeout(closeModal, 800);
                    } catch (err) {
                        if (statusMsg) {
                            statusMsg.textContent = '연결 실패: ' + err.message;
                            statusMsg.className = 'modal-status-msg error';
                        }
                    }
                });
            }

            this.openCloudModal = openModal;
        }
    }

    // =========================================================================
    // 10. 애플리케이션 진입점 (Application Entry Point)
    // =========================================================================
    document.addEventListener('DOMContentLoaded', () => {
        const gridEl = document.getElementById('grid');
        const tooltipEl = document.getElementById('tooltip');

        if (!gridEl) {
            console.error('[NoteApp] #grid element not found!');
            return;
        }

        // 1. 뷰포트 & 그리드
        const viewport = new ViewportManager(gridEl, tooltipEl);

        // 2. 요소 저장소 (Box / Line)
        const store = new ElementStore(gridEl, viewport);

        // 3. 선택 관리자
        const selectionManager = new SelectionManager();

        // 4. 데이터 관리자 (GitHub REST API & data.json)
        const dataManager = new DataManager(store, viewport);

        // 5. 실행 취소 / 다시 실행 관리자 (History Manager)
        const historyManager = new HistoryManager(store, viewport, selectionManager, dataManager);
        selectionManager.historyManager = historyManager;

        // 6. 텍스트 편집 관리자
        const textEditor = new TextEditorManager(store, selectionManager, historyManager);
        store.textEditor = textEditor;

        // 7. 생성 모드 관리자 (Box / Line 추가)
        const addModeManager = new AddModeManager(store, selectionManager, textEditor);

        // 8. 인터랙션 & 변형 관리자
        const interaction = new InteractionManager(viewport, store, selectionManager, textEditor, addModeManager, historyManager, dataManager);
        addModeManager.interactionManager = interaction;

        // 9. 초기 데이터 로드 및 이벤트 바인딩
        dataManager.loadInitialData();
        dataManager.bindFileInput();
        dataManager.bindCloudModal();

        // 전역 접근용 네임스페이스 등록
        window.NoteApp = {
            viewport,
            store,
            selectionManager,
            historyManager,
            textEditor,
            addModeManager,
            interaction,
            dataManager,
            config: CONFIG
        };

        console.log('[NoteApp] Note Initialized Successfully - GitHub REST API Sync & 10s Auto-save Enabled');
    });

})();
