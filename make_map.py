import pandas as pd
import folium
from geopy.geocoders import Nominatim
from geopy.extra.rate_limiter import RateLimiter
from tqdm import tqdm
from branca.colormap import LinearColormap
import sys
import os
import json
from branca.element import MacroElement
from jinja2 import Template
import colorsys
from html import escape
import re
import datetime
import calendar
import os
import shutil
import subprocess
import sys

REPO_DIR = os.path.dirname(os.path.abspath(__file__))


def make_palette(n):
    """Return n visually distinct hex colors."""
    base = [
        "#e6194b", "#3cb44b", "#4363d8", "#f58231", "#911eb4",
        "#46f0f0", "#f032e6", "#9a6324", "#008080", "#808000",
        "#000075", "#e6b800", "#800000", "#aaffc3", "#fabed4",
        "#469990", "#dcbeff", "#ffd8b1", "#a9a9a9", "#bcf60c",
    ]
    if n <= len(base):
        return base[:n]
    colors = list(base)
    # past 20 categories, generate extra hues using the golden ratio
    h = 0.0
    while len(colors) < n:
        h = (h + 0.618033988749895) % 1
        r, g, b = colorsys.hsv_to_rgb(h, 0.65, 0.85)
        colors.append("#%02x%02x%02x" % (int(r*255), int(g*255), int(b*255)))
    return colors

def norm(v):
    """Normalize a cell so values compare equal after a CSV round trip
    (e.g. 7 vs 7.0, '02134' vs 2134, NaN vs empty string)."""
    if pd.isna(v):
        return ""
    s = str(v).strip()
    try:
        return format(float(s), ".10g")
    except ValueError:
        return s
    
_MONTH_RE = re.compile(
    r"\b(jan(?:uary)?|feb(?:ruary)?|mar(?:ch)?|apr(?:il)?|may|june?|july?|aug(?:ust)?|"
    r"sep(?:t(?:ember)?)?|oct(?:ober)?|nov(?:ember)?|dec(?:ember)?)\b"
)
_MONTH_NUM = {m: i + 1 for i, m in enumerate(
    ["jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec"])}

_RANGE_SEP = re.compile(r"^(?:-|–|—|to|through|thru|until)$")

def parse_months(v):
    """Return a list of months (1-12) from a date or free text, or [] if none found.
    'January-March' -> [1,2,3]; 'May, June, July, August' -> [5,6,7,8];
    'Nov-Feb' -> [11,12,1,2]; 'June 5-7' -> [6]; 'Jun 28 - Jul 2' -> [6,7]."""
    if v is None or pd.isna(v):
        return []
    if isinstance(v, datetime.date):          # also covers pd.Timestamp / datetime
        return [v.month]
    s = str(v).strip().lower()
    if not s:
        return []

    found = [(m.start(), m.end(), _MONTH_NUM[m.group(1)[:3]]) for m in _MONTH_RE.finditer(s)]
    if found:
        months = []
        def add(n):
            if n not in months:
                months.append(n)

        add(found[0][2])
        for prev, cur in zip(found, found[1:]):
            # text between two month names, minus day numbers (5, 5th), periods and spaces
            sep = re.sub(r"\d+(?:st|nd|rd|th)?|\s+|\.", "", s[prev[1]:cur[0]])
            if _RANGE_SEP.match(sep) and prev[2] != cur[2]:
                n = prev[2]
                while n != cur[2]:            # walk forward, wrapping Dec -> Jan
                    n = n % 12 + 1
                    add(n)
            else:
                add(cur[2])
        return months

    m = re.match(r"(\d{4})-(\d{1,2})-\d{1,2}", s)        # 2026-06-05
    if m and 1 <= int(m.group(2)) <= 12:
        return [int(m.group(2))]
    m = re.match(r"(\d{1,2})/\d{1,2}", s)                # 6/5 or 6/5/2026
    if m and 1 <= int(m.group(1)) <= 12:
        return [int(m.group(1))]
    return []

################################################################################


class ColorToggle(MacroElement):
    """Color modes: priority / category / seen / event. The priority slider filters in all modes;
    legend checkboxes filter by category (category mode), seen (seen mode) or month (event mode,
    which shows event/festival markers only)."""
    _template = Template("""
    {% macro script(this, kwargs) %}
    (function() {
        var styles = {{ this.styles_json }};
        var legend = {{ this.legend_json }};
        var monthLegend = {{ this.month_json }};   // [[month, label, color], ...]; month 0 = unknown
        var monthColor = {};
        monthLegend.forEach(function(m) { monthColor[m[0]] = m[2]; });
        var map = {{ this._parent.get_name() }};
        var hidden = {};                                   // category -> true when unchecked
        var hiddenSeen = {seen: false, notseen: false};    // true when unchecked
        var hiddenMonth = {};                              // month -> true when unchecked
        var mode = 'priority';                             // 'priority' | 'category' | 'seen' | 'event'
        var lo = 0, hi = 10;                               // priority range
        var linkStyle = 'color:#0078a8; cursor:pointer; text-decoration:underline;';
        var rowStyle = 'display:block; cursor:pointer; margin:0; white-space:nowrap;';

        var css = document.createElement('style');
        css.textContent =
            '.prio-slider{position:relative;width:180px;height:22px;margin-top:4px;}' +
            '.prio-track{position:absolute;left:0;right:0;top:9px;height:4px;border-radius:2px;' +
            'background:linear-gradient(to right,red,yellow,green);}' +
            '.prio-slider input[type=range]{position:absolute;left:0;top:0;width:100%;height:22px;margin:0;' +
            'background:none;pointer-events:none;-webkit-appearance:none;appearance:none;}' +
            '.prio-slider input[type=range]::-webkit-slider-runnable-track{background:none;}' +
            '.prio-slider input[type=range]::-moz-range-track{background:none;}' +
            '.prio-slider input[type=range]::-webkit-slider-thumb{pointer-events:auto;-webkit-appearance:none;' +
            'width:14px;height:14px;border-radius:50%;background:#fff;border:2px solid #333;cursor:pointer;}' +
            '.prio-slider input[type=range]::-moz-range-thumb{pointer-events:auto;' +
            'width:10px;height:10px;border-radius:50%;background:#fff;border:2px solid #333;cursor:pointer;}';
        document.head.appendChild(css);

        function inRange(p) {
            if (lo <= 0 && hi >= 10) { return true; }        // full range: show everything, incl. missing scores
            if (p === null || p === undefined) { return false; }
            return p >= lo - 1e-9 && p <= hi + 1e-9;
        }

        function applyVisibility() {
            // the month filter is "on" once any month is unchecked
            var monthOn = false;
            for (var k in hiddenMonth) { if (hiddenMonth[k]) { monthOn = true; } }

            for (var name in styles) {
                var layer = window[name];
                var s = styles[name];
                var monthOk = s.is_event && s.months.some(function(m) { return !hiddenMonth[m]; });
                var show = inRange(s.p) &&
                           !hidden[s.cat] &&
                           !hiddenSeen[s.is_seen ? 'seen' : 'notseen'] &&
                           ((mode !== 'event' && !monthOn) || monthOk);
                if (show && !map.hasLayer(layer)) { map.addLayer(layer); }
                else if (!show && map.hasLayer(layer)) { map.removeLayer(layer); }
            }
            if (mode === 'event') { applyColors(); }
        }

        function eventColor(s) {
            var shown = s.months.filter(function(m) { return !hiddenMonth[m]; });
            return monthColor[shown.length ? shown[0] : s.months[0]];
        }

        function applyColors() {
            for (var name in styles) {
                var s = styles[name];
                var c = (mode === 'event') ? eventColor(s) : s[mode];
                window[name].setStyle({color: c, fillColor: c});
            }
        }

        function applyMode() {
            applyColors();
            applyVisibility();
            document.getElementById('category-legend').style.display = mode === 'category' ? 'block' : 'none';
            document.getElementById('event-legend').style.display = mode === 'event' ? 'block' : 'none';
        }

        // Builds a checkbox legend with All / None links. items = [[key, label, color], ...]
        function buildFilterList(id, items, hiddenMap) {
            var box = document.createElement('div');
            box.id = id;
            box.style.cssText = 'display:none; margin-top:4px; font-size:12px; max-height:300px; overflow-y:auto;';

            var links = document.createElement('div');
            links.style.cssText = 'margin-bottom:4px;';
            var allLink = document.createElement('span');
            allLink.style.cssText = linkStyle;
            allLink.textContent = 'All';
            var noneLink = document.createElement('span');
            noneLink.style.cssText = linkStyle;
            noneLink.textContent = 'None';
            links.appendChild(allLink);
            links.appendChild(document.createTextNode(' | '));
            links.appendChild(noneLink);
            box.appendChild(links);

            var cbs = [];
            items.forEach(function(it) {
                var row = document.createElement('label');
                row.style.cssText = rowStyle;
                var cb = document.createElement('input');
                cb.type = 'checkbox';
                cb.checked = true;
                cb.addEventListener('change', function() {
                    hiddenMap[it[0]] = !cb.checked;
                    applyVisibility();
                });
                cbs.push([it[0], cb]);
                var dot = document.createElement('span');
                dot.style.color = it[2];
                dot.innerHTML = ' &#9679; ';
                row.appendChild(cb);
                row.appendChild(dot);
                row.appendChild(document.createTextNode(it[1]));
                box.appendChild(row);
            });

            function setAll(checked) {
                cbs.forEach(function(pair) {
                    pair[1].checked = checked;
                    hiddenMap[pair[0]] = !checked;
                });
                applyVisibility();
            }
            allLink.addEventListener('click', function() { setAll(true); });
            noneLink.addEventListener('click', function() { setAll(false); });
            return box;
        }

        var control = L.control({position: 'topright'});
        control.onAdd = function() {
            var div = L.DomUtil.create('div', 'leaflet-bar');
            div.style.background = 'white';
            div.style.padding = '6px 10px';

            // ---- color mode selector ----
            var modes = document.createElement('div');
            modes.style.cssText = 'font-size:12px;';
            [['priority', 'By Priority'],
             ['category', 'By Category'],
             ['event', 'Annual Events']].forEach(function(m) {
                var lbl = document.createElement('label');
                lbl.style.cssText = rowStyle;
                var rb = document.createElement('input');
                rb.type = 'radio';
                rb.name = 'color-mode';
                rb.value = m[0];
                rb.checked = (m[0] === 'priority');
                rb.addEventListener('change', function() {
                    if (rb.checked) { mode = m[0]; applyMode(); }
                });
                lbl.appendChild(rb);
                lbl.appendChild(document.createTextNode(' ' + m[1]));
                modes.appendChild(lbl);
            });
            div.appendChild(modes);

            // ---- priority range slider ----
            var prioBox = document.createElement('div');
            prioBox.id = 'priority-filter';
            prioBox.style.cssText = 'margin-top:6px; font-size:12px;';
            prioBox.innerHTML =
                'Priority: <b id="prio-label">0.0 &ndash; 10.0</b>' +
                '<div class="prio-slider"><div class="prio-track"></div>' +
                '<input type="range" id="prio-min" min="0" max="10" step="0.1" value="0">' +
                '<input type="range" id="prio-max" min="0" max="10" step="0.1" value="10"></div>' +
                '<span id="prio-reset" style="' + linkStyle + '">Reset</span>';
            div.appendChild(prioBox);


            // ---- seen filter (applies in every color mode) ----
            var seenBox = document.createElement('div');
            seenBox.id = 'seen-filter';
            seenBox.style.cssText = 'margin-top:6px; font-size:12px;';
            seenBox.innerHTML =
                '<label style="' + rowStyle + '"><input type="checkbox" id="seen-cb" checked> Seen</label>' +
                '<label style="' + rowStyle + '"><input type="checkbox" id="notseen-cb" checked> Not seen</label>';

            seenBox.querySelector('#seen-cb').addEventListener('change', function() {
                hiddenSeen.seen = !this.checked;
                applyVisibility();
            });
            seenBox.querySelector('#notseen-cb').addEventListener('change', function() {
                hiddenSeen.notseen = !this.checked;
                applyVisibility();
            });
            div.appendChild(seenBox);

            // ---- category legend ----
            var catItems = Object.keys(legend).map(function(cat) { return [cat, cat, legend[cat]]; });
            div.appendChild(buildFilterList('category-legend', catItems, hidden));

            // ---- event month legend ----
            div.appendChild(buildFilterList('event-legend', monthLegend, hiddenMonth));

            // ---- slider behavior ----
            var minIn = prioBox.querySelector('#prio-min');
            var maxIn = prioBox.querySelector('#prio-max');
            var lab = prioBox.querySelector('#prio-label');

            function syncSlider() {
                lab.textContent = lo.toFixed(1) + ' \\u2013 ' + hi.toFixed(1);
                minIn.style.zIndex = lo > 5 ? 3 : 1;
                maxIn.style.zIndex = lo > 5 ? 1 : 3;
                applyVisibility();
            }
            minIn.addEventListener('input', function() {
                lo = Math.min(parseFloat(minIn.value), hi);
                minIn.value = lo;
                syncSlider();
            });
            maxIn.addEventListener('input', function() {
                hi = Math.max(parseFloat(maxIn.value), lo);
                maxIn.value = hi;
                syncSlider();
            });
            prioBox.querySelector('#prio-reset').addEventListener('click', function() {
                lo = 0; hi = 10; minIn.value = 0; maxIn.value = 10;
                syncSlider();
            });

            L.DomEvent.disableClickPropagation(div);
            L.DomEvent.disableScrollPropagation(div);
            return div;
        };
        control.addTo(map);
                         
        // ---- seen / not seen counts (bottom right) ----
        var nSeen = 0, nNotSeen = 0;
        for (var nm in styles) {
            if (styles[nm].is_seen) { nSeen++; } else { nNotSeen++; }
        }
        var counts = L.control({position: 'bottomright'});
        counts.onAdd = function() {
            var d = L.DomUtil.create('div', 'leaflet-bar');
            d.style.cssText = 'background:white; padding:6px 10px; font-size:13px; color:black; line-height:1.5;';
            d.innerHTML =
                'Places seen: <b style="color:#00a000;">' + nSeen + '</b><br>' +
                'Yet to see: <b style="color:#d00000;">' + nNotSeen + '</b>';
            L.DomEvent.disableClickPropagation(d);
            return d;
        };
        counts.addTo(map);
    })();
    {% endmacro %}
    """)

    def __init__(self, styles, legend, seen_color, not_seen_color, month_legend):
        super().__init__()
        self._name = "ColorToggle"
        self.styles_json = json.dumps(styles)
        self.legend_json = json.dumps(legend)
        self.month_json = json.dumps(month_legend)
        self.seen_color = seen_color
        self.not_seen_color = not_seen_color

################################################################################

def process_file(path):
    """
    Process a file with a tab for each state/coutnry
    """

    sheets = pd.read_excel(path, sheet_name=None)
    sheets.pop('Template')
    dfs = list(sheets.values())

    for df in dfs:
        df.columns = [col.upper() for col in df.columns]
        if 'STREET ADDRESS' in df.columns:
            df['ADDRESS'] = df['STREET ADDRESS']

    df = pd.concat(dfs, ignore_index=True)

    kept_cols = ['NAME','ADDRESS','CITY','STATE','ZIP CODE', 'CATEGORY', 'PRIORITY','SCHEDULING RESTRICTIONS','NOTES']
    df = df[kept_cols]

    # update categories
    for i in range(len(df)):
        cat = df.at[i,'CATEGORY']
        cat = cat.lower()

        if cat == 'hike':
            cat = 'hiking'
        if cat == 'naturural site':
            cat = 'natural site'
        if cat == 'nps siite':
            cat = 'nps site'
        if cat == 'attaraction':
            cat = 'attraction'
        if cat == 'event':
            cat = 'event/festival'
        if cat == 'festival':
            cat = 'event/festival'
        if cat == 'historical site' or cat == 'historic site' or cat == 'historical area':
            cat = 'historic(al) site'
        if cat == 'city':
            cat = 'attraction'
        if cat == 'state parlk':
            cat = 'state park'
        if cat == 'wildlife':
            cat = 'wildlife viewing'
        if cat == 'wildlife viewing, hiking':
            cat = 'hiking'
        if cat == 'paddling/snorkeling/hiking' or cat == 'paddling' or cat == 'snorkeling':
            cat = 'outdoor recreation'
        if cat == 'telescope':
            cat = 'attraction'
        if cat == 'cemetary':
            cat == 'attraction'
        if cat == 'musuem':
            cat = 'museum'
        if cat == 'library':
            cat = 'museum'
        if cat == 'state capitol':
            cat = 'attraction'

        df.at[i,'CATEGORY'] = cat


        # adjust zip code
        try:
            zc = str(df.at[i, 'ZIP CODE'])
            if '.' in zc:
                zc = zc.split(".")[0]
            if len(zc) == 4 and zc.isnumeric():
                zc = "0" + zc
            df.at[i, 'ZIP CODE'] = zc
        except:
            print(df.iloc[i])

    # make new column for concatenated address strings
    address_strings = []
    for i in range(len(df)):
        addr = str(df.at[i, 'ADDRESS'])
        city = str(df.at[i,'CITY'])
        state = str(df.at[i, 'STATE'])
        zip_code = str(df.at[i, 'ZIP CODE'])

        address_string = addr + "; " + city + ", " + state + "; " + zip_code 
        address_strings.append(address_string)


    df['ADDRESS STRING'] = address_strings

    ############################################################################

    # query (and cache) lat/lons
    # update cache if anything in new file has changed

    geolocator = Nominatim(user_agent="address_priority_mapper")  # use something unique
    geocode = RateLimiter(geolocator.geocode, min_delay_seconds=1.1)
    ADDRESS_COL = 'ADDRESS STRING'
    CACHE_FILE = "geocoded_addresses.csv"

    # a row matches the cache only if every one of these columns is identical
    KEY_COLS = kept_cols + [ADDRESS_COL]

    def row_key(r):
        return tuple(norm(r[c]) for c in KEY_COLS)

    # load cache: full-row key -> (lat, lon)
    cached = {}
    try:
        disk_cache = pd.read_csv(CACHE_FILE)
        for _, r in disk_cache.iterrows():
            if pd.notna(r["lat"]) and pd.notna(r["lon"]):
                cached[row_key(r)] = (float(r["lat"]), float(r["lon"]))
    except Exception:
        cached = {}   # no cache yet, or an old-format cache: geocode everything

    # reuse exact matches, geocode everything else
    looked_up = {}    # address string -> coords, so identical addresses are only geocoded once per run
    lats, lons = [], []
    n_cached = n_geocoded = 0

    for _, r in tqdm(df.iterrows(), total=len(df)):
        key = row_key(r)
        if key in cached:
            lat, lon = cached[key]
            n_cached += 1
        else:
            addr = r[ADDRESS_COL]
            if addr not in looked_up:
                # try to geocode whole address string
                loc = geocode(addr)

                # try to geocode city + state + zip
                if loc is None:
                    loc = geocode(addr.split(";")[1] + ", " + addr.split(";")[2])

                # try to geocode zip
                if loc is None:
                    loc = geocode(addr.split(";")[2])

                looked_up[addr] = (loc.latitude, loc.longitude) if loc else (None, None)
            lat, lon = looked_up[addr]
            n_geocoded += 1
        lats.append(lat)
        lons.append(lon)

    df["lat"] = lats
    df["lon"] = lons

    mapped = df.dropna(subset=["lat", "lon"]).copy()
    mapped.to_csv(CACHE_FILE, index=False)   # cache now mirrors the current file
    print(f"Geocoded {n_geocoded} rows, reused {n_cached} cached rows")

    ############################################################################

    with open("carto_key.txt", "r", encoding="utf-8") as f:
        api_key = f.readline().rstrip("\n")


    PRIORITY_COL = "PRIORITY"   # float, 0-10
    LABEL_COL = "NAME"             # text shown on hover
    OUTPUT_HTML = "index.html"

    colormap = LinearColormap(
        colors=["red", "yellow", "green"],
        vmin=0,
        vmax=10,
        caption="Priority (0-10)",
    )

    m = folium.Map(
        location=[mapped["lat"].mean(), mapped["lon"].mean()],
        zoom_start=10,
        tiles=None
    )

    folium.TileLayer(
        tiles="https://basemaps.cartocdn.com/rastertiles/voyager/{z}/{x}/{y}.png?key=cb1_4inf_1_798563bfdbece5d602024372",
        attr='&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> contributors &copy; <a href="https://carto.com/attributions">CARTO</a>',
        name="CARTO Voyager",
        max_zoom=20,
    ).add_to(m)

    # one color per distinct category value
    categories = sorted(mapped["CATEGORY"].dropna().astype(str).str.strip().unique())
    category_colors = dict(zip(categories, make_palette(len(categories))))
    MISSING_COLOR = "#888888"
    marker_styles = {}
    SEEN_COLOR = "#00a000"
    NOT_SEEN_COLOR = "#d00000"
    MONTH_COLORS = [
        "#4363d8", "#911eb4", "#f032e6", "#e6194b", "#f58231", "#e6b800",
        "#bcf60c", "#3cb44b", "#008080", "#46f0f0", "#9a6324", "#000075",
    ]   # Jan ... Dec
    EVENT_ERROR_COLOR = "#000000"   # events whose month couldn't be determined
    month_legend = [[i + 1, calendar.month_name[i + 1], MONTH_COLORS[i]] for i in range(12)]
    month_legend.append([0, "Unknown date", EVENT_ERROR_COLOR])

    for _, row in mapped.iterrows():
        p = row[PRIORITY_COL]
        cat = str(row["CATEGORY"]).strip()
        color = colormap(p) if pd.notna(p) else "#888888"

        has_sched = pd.notna(row["SCHEDULING RESTRICTIONS"]) and bool(str(row["SCHEDULING RESTRICTIONS"]).strip())
        notes = row["NOTES"]
        notes_text = escape(str(notes).strip()) if pd.notna(notes) and str(notes).strip() else "n/a"
        sched = row["SCHEDULING RESTRICTIONS"]
        sched_text = escape(str(sched).strip()) if pd.notna(sched) and str(sched).strip() else "n/a"
        prio_text = f"{p:.1f}" if pd.notna(p) else "n/a"

        lines = [
            f"<b>{escape(str(row[LABEL_COL]))}</b>",
            f"Priority: {prio_text}",
        ]
        if has_sched:
            lines.append(f"Scheduling: {sched_text}")
        if notes_text != "n/a":
            lines.append(f"Notes: {notes_text}")
        tooltip_html = "<br>".join(lines)

        marker = folium.CircleMarker(
            location=[row["lat"], row["lon"]],
            radius=7,
            color=color,
            fill=True,
            fill_color=color,
            fill_opacity=0.85,
            weight=1,
            tooltip=folium.Tooltip(tooltip_html),
            popup=folium.Popup(
                f"<b>{row[LABEL_COL]}</b><br>{row[ADDRESS_COL]}<br>"
                f"Category: {row['CATEGORY']}<br>Priority: {p:.2f}"
                if pd.notna(p) else
                f"<b>{row[LABEL_COL]}</b><br>{row[ADDRESS_COL]}<br>"
                f"Category: {row['CATEGORY']}<br>Priority: n/a",
                max_width=300,
            ),
        ).add_to(m)

        seen = str(row["NOTES"]).strip().lower() == "seen!"
        is_event = has_sched
        months = parse_months(row["SCHEDULING RESTRICTIONS"]) if is_event else []   # <- column holding the event date
        marker_styles[marker.get_name()] = {
            "priority": color,
            "category": category_colors.get(cat, MISSING_COLOR),
            "seen": SEEN_COLOR if seen else NOT_SEEN_COLOR,
            "is_seen": seen,
            "is_event": is_event,
            "months": months or [0],      # 0 = unknown date
            "cat": cat,
            "p": float(p) if pd.notna(p) else None,
        }

    m.fit_bounds(mapped[["lat", "lon"]].values.tolist())

    ColorToggle(marker_styles, category_colors, SEEN_COLOR, NOT_SEEN_COLOR, month_legend).add_to(m)
    m.save(OUTPUT_HTML)
    print(f"Saved {OUTPUT_HTML} with {len(mapped)} places of interest")

def run_git(*args):
    result = subprocess.run(
        ["git", "-C", REPO_DIR, *args],
        capture_output=True, text=True,
        creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
    )
    if result.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed:\n{result.stderr.strip()}")
    return result.stdout

def push_to_git():
    
    dest = os.path.join(REPO_DIR, "index.html")

    run_git("add", dest)

    # Skip the commit if nothing changed (commit would error otherwise)
    if run_git("status", "--porcelain", dest).strip():
        run_git("commit", "-m", f"Update index.html")
        run_git("push")
        print("Pushed to git.")
    else:
        print("No changes to push.")


if __name__ == "__main__":

    try:
        input_path = os.path.abspath(sys.argv[1]) # TODO: uncomment
        #input_path = os.path.abspath(r"file.xlsx") # TODO: delete
        process_file(input_path)
        push_to_git()

    except Exception as e:
        print(f"Error: {e}")
        input("Press Enter to exit...")  # keeps the window open so you can read it
        sys.exit(1)