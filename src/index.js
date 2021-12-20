import Delaunator from 'delaunator';

const { GUI } = require('dat.gui');
const useGUI = true;

const canvasSketch = require('canvas-sketch');
const { clamp, lerp } = require('canvas-sketch-util/math');
// const Color = require('canvas-sketch-util/color');
const { getBounds } = require('canvas-sketch-util/geometry');
const Random = require('canvas-sketch-util/random');
const svg = require('./canvas-to-svg.js');
const chromotome = require('chromotome');
// const Delaunator = require('delaunator');
const geometric = require('geometric');

const defaultBackgroundColor = '#ffffff';
const defaultColorLibrary = 'niceColorPalettes';

// Some factors to modulate the line width/spacing
const minLineSpaceFactor = 2;
const maxLineSpaceFactor = 20;
const spaceFactorMean = 2;
const spaceFactorDeviation = 5;

const data = {
  backgroundColor: defaultBackgroundColor,
  colors: [],
  colorLibrary: defaultColorLibrary,
  colorLibraryNames: ['chromotome', 'niceColorPalettes'],
  distortion: 10,
  fillTriangles: true,
  gridSize: 50,
  gridGap: 0,
  hatchLines: false,
  hatchLineLayers: 2,
  minimumAngle: 1,
  randomSeed: Random.getRandomSeed() * 1,
  showGrid: false,
  useBackgroundColor: true
};

const settings = {
  data,
  dimensions: [4096, 4096],
  suffix: data.randomSeed
};

const colorLibraries = {
  chromotome: chromotome.getAll(),
  niceColorPalettes: require('nice-color-palettes')
};

const getUV = (val, count) => {
  return count <= 1 ? 0.5 : val / (count - 1);
};

const deg2rad = degrees => {
  return (degrees * 180) / Math.PI;
};

// http://stackoverflow.com/a/7505937
// Center point is p1; angle returned in radians
function findAngle(p0, p1, p2, inDegrees = false) {
  const b = Math.pow(p1[0] - p0[0], 2) + Math.pow(p1[1] - p0[1], 2);
  const a = Math.pow(p1[0] - p2[0], 2) + Math.pow(p1[1] - p2[1], 2);
  const c = Math.pow(p2[0] - p0[0], 2) + Math.pow(p2[1] - p0[1], 2);
  const angle = Math.acos((a + b - c) / Math.sqrt(4 * a * b));
  return inDegrees ? angle : deg2rad(angle);
}

const findAngles = (p0, p1, p2) => {
  const angle0 = findAngle(p0, p1, p2);
  const angle1 = findAngle(p1, p2, p0);
  const angle2 = findAngle(p2, p0, p1);
  return [angle0, angle1, angle2];
};

const getScaleFactor = val => {
  return val > 0 ? Math.abs(1 - val / 10) : 1;
};

// From: https://github.com/rough-stuff/rough/blob/master/src/fillers/scan-line-hachure.ts
const straightHachureLines = (points, o) => {
  const vertices = [...points];
  if (vertices[0].join(',') !== vertices[vertices.length - 1].join(',')) {
    vertices.push([vertices[0][0], vertices[0][1]]);
  }
  const lines = [];
  if (vertices && vertices.length > 2) {
    let gap = o.gap;
    if (gap < 0) {
      gap = o.strokeWidth * 4;
    }
    gap = Math.max(gap, 0.1);

    // Create sorted edges table
    const edges = [];
    for (let i = 0; i < vertices.length - 1; i++) {
      const p1 = vertices[i];
      const p2 = vertices[i + 1];
      if (p1[1] !== p2[1]) {
        const ymin = Math.min(p1[1], p2[1]);
        edges.push({
          ymin,
          ymax: Math.max(p1[1], p2[1]),
          x: ymin === p1[1] ? p1[0] : p2[0],
          islope: (p2[0] - p1[0]) / (p2[1] - p1[1])
        });
      }
    }
    edges.sort((e1, e2) => {
      if (e1.ymin < e2.ymin) {
        return -1;
      }
      if (e1.ymin > e2.ymin) {
        return 1;
      }
      if (e1.x < e2.x) {
        return -1;
      }
      if (e1.x > e2.x) {
        return 1;
      }
      if (e1.ymax === e2.ymax) {
        return 0;
      }
      return (e1.ymax - e2.ymax) / Math.abs(e1.ymax - e2.ymax);
    });
    if (!edges.length) {
      return lines;
    }

    // Start scanning
    let activeEdges = [];
    let y = edges[0].ymin;
    while (activeEdges.length || edges.length) {
      if (edges.length) {
        let ix = -1;
        for (let i = 0; i < edges.length; i++) {
          if (edges[i].ymin > y) {
            break;
          }
          ix = i;
        }
        const removed = edges.splice(0, ix + 1);
        removed.forEach(edge => {
          activeEdges.push({ s: y, edge });
        });
      }
      activeEdges = activeEdges.filter(ae => {
        if (ae.edge.ymax <= y) {
          return false;
        }
        return true;
      });
      activeEdges.sort((ae1, ae2) => {
        if (ae1.edge.x === ae2.edge.x) {
          return 0;
        }
        return (ae1.edge.x - ae2.edge.x) / Math.abs(ae1.edge.x - ae2.edge.x);
      });

      // fill between the edges
      if (activeEdges.length > 1) {
        for (let i = 0; i < activeEdges.length; i = i + 2) {
          const nexti = i + 1;
          if (nexti >= activeEdges.length) {
            break;
          }
          const ce = activeEdges[i].edge;
          const ne = activeEdges[nexti].edge;
          lines.push([[Math.round(ce.x), y], [Math.round(ne.x), y]]);
        }
      }

      y += gap;
      activeEdges.forEach(ae => {
        ae.edge.x = ae.edge.x + gap * ae.edge.islope;
      });
    }
  }
  return lines;
};

// From: https://github.com/rough-stuff/rough/blob/master/src/fillers/scan-line-hachure.ts
const polygonHachureLines = (points, o) => {
  const rotationCenter = [0, 0];
  const angle = Math.round(o.angle);
  if (angle) {
    rotatePoints(points, rotationCenter, angle);
  }
  const lines = straightHachureLines(points, o);
  if (angle) {
    rotatePoints(points, rotationCenter, -angle);
    rotateLines(lines, rotationCenter, -angle);
  }
  return lines;
};

// From: https://github.com/rough-stuff/rough/blob/master/src/fillers/scan-line-hachure.ts
const rotateLines = (lines, center, degrees) => {
  const points = [];
  lines.forEach(line => points.push(...line));
  rotatePoints(points, center, degrees);
};

// From: https://github.com/rough-stuff/rough/blob/master/src/fillers/scan-line-hachure.ts
const rotatePoints = (points, center, degrees) => {
  if (points && points.length) {
    const [cx, cy] = center;
    const angle = (Math.PI / 180) * degrees;
    const cos = Math.cos(angle);
    const sin = Math.sin(angle);
    points.forEach(p => {
      const [x, y] = p;
      p[0] = (x - cx) * cos - (y - cy) * sin + cx;
      p[1] = (x - cx) * sin + (y - cy) * cos + cy;
    });
  }
};

const sketch = props => {
  // Allow export as SVG
  return svg(props => {
    const { context, data, width, height } = props;
    const margin = width * 0.02;
    // A base line width for all polygons
    const lineWidth = width * 0.002;

    Random.setSeed(data.randomSeed);
    // Random.setSeed(575310);
    // console.log(`seed: ${data.randomSeed}`);

    context.fillStyle = data.backgroundColor;
    context.fillRect(0, 0, width, height);

    const palettes = colorLibraries[data.colorLibrary];

    // Nonsense to deal with switching between color libraries
    // (chromotome vs. nice-color-palettes)
    const palette = Random.pick(palettes);
    data.colors = palette.colors || palette;

    const createGrid = () => {
      const gridItems = [];
      let odd = true;

      for (let y = 0; y < data.gridSize; y++) {
        odd = !odd;
        for (let x = 0; x < data.gridSize; x++) {
          // Shift 1/2 every other row to create triangle grid
          let u = getUV(odd ? x : x + 0.5, data.gridSize);
          let v = getUV(y, data.gridSize);

          let distortion = data.distortion / 100;

          // At some point at Poisson-disc sampling for better variation
          u = u + Random.sign() * Random.noise2D(x, y) * distortion;
          v = v + Random.sign() * Random.noise2D(x, y) * distortion;

          // Reject any grid items that are outside of our bounds
          if (u >= 0 && v >= 0 && u <= 1 && v <= 1) {
            gridItems.push({
              position: [u, v]
            });
          }
        }
      }

      return gridItems;
    };

    const drawTriangle = (coords, fillColor) => {
      const isAboveThreshold = angle => angle > data.minimumAngle;

      const [p0, p1, p2] = coords;
      const [x0, y0] = p0;
      const [x1, y1] = p1;
      const [x2, y2] = p2;
      const angles = findAngles(p0, p1, p2);

      // Eliminate any extreme triangles
      if (angles.every(isAboveThreshold)) {
        // Draw triangle
        context.beginPath();
        context.moveTo(x0, y0);
        context.lineTo(x1, y1);
        context.lineTo(x2, y2);
        context.lineTo(x0, y0);
        context.closePath();

        if (data.fillTriangles) {
          context.fillStyle = fillColor;
          // const color = Random.pick(data.colors);
          // const shift = Random.sign() *
          //   Math.floor(Math.min(1, Random.gaussian(.1, .5)) * 100);
          // const fillColor = Color.offsetHSL(color, 0, shift, 0);
          // context.fillStyle = fillColor.hex;
          context.fill();
        }
      }
    };

    const points = [];
    const grid = createGrid();

    grid.forEach(gridItem => {
      const { position } = gridItem;
      const [u, v] = position;

      // Interpolate points between min / max of page bounds
      let x = lerp(margin, width - margin, u);
      let y = lerp(margin, height - margin, v);

      points.push([x, y]);
      // console.log(points);

      // Grid dots
      if (data.showGrid) {
        context.beginPath();
        context.fillStyle = 'red';
        context.arc(x, y, 10, 0, 2 * Math.PI, true);
        context.fill();
        context.closePath();
      }
    });

    // Calculate Delaunay triangles from grid
    let delaunay = Delaunator.from(points);
    let { triangles } = delaunay;
    let coordinates = [];
    for (let i = 0; i < triangles.length; i += 3) {
      coordinates.push([
        points[triangles[i]],
        points[triangles[i + 1]],
        points[triangles[i + 2]]
      ]);
    }

    let paths = [];
    let hatchLines = [];
    let hatchLineCoords;

    // Scale polygon shapes using gap value
    let scaleFactor = getScaleFactor(data.gridGap);
    coordinates = coordinates.map(coords => {
      return geometric.polygonScale(coords, scaleFactor);
    });

    coordinates.forEach(coords => {
      // Add triangle paths
      let fillColor = Random.pick(data.colors);
      // let scaledPolygon = geometric.polygonScale(coords, scaleFactor);

      paths.push({
        fillColor,
        coords
      });

      // Add hatch lines
      if (data.hatchLines) {
        // Draw random number of hatch lines for each triangle
        for (
          let index = 0;
          index < Random.range(1, data.hatchLineLayers);
          index++
        ) {
          // Determine a nice value to modulate the line spacing
          let spaceFactor = Math.abs(
            Random.gaussian(spaceFactorMean, spaceFactorDeviation)
          );
          let lineSpacing =
            lineWidth *
            clamp(spaceFactor, minLineSpaceFactor, maxLineSpaceFactor);
          // Calculate hatch lines
          hatchLineCoords = polygonHachureLines(coords, {
            angle: Random.range(-180, 180),
            gap: lineSpacing
          });
          // Construct array of hatch line objects
          hatchLines.push({
            color: Random.pick(data.colors),
            lines: hatchLineCoords
          });
        }
      }
    });

    // Draw triangles
    paths.forEach(({ coords, fillColor }) => {
      drawTriangle(coords, fillColor);
    });

    hatchLines.forEach(({ color, lines }) => {
      lines.forEach(line => {
        let [from, to] = line;
        let [x0, y0] = from;
        let [x1, y1] = to;
        context.beginPath();
        context.lineCap = 'round';
        context.strokeStyle = color;
        context.lineWidth = lineWidth;
        context.moveTo(x0, y0);
        context.lineTo(x1, y1);
        context.closePath();
        context.stroke();
      });
    });
  });
};

(async () => {
  const manager = await canvasSketch(sketch, settings);
  let gui;
  let controllers = [];

  if (useGUI) {
    gui = new GUI();

    controllers.push(
      add(gui, data, 'randomSeed', 0, 999999)
        .step(1)
        .name('Random seed')
    );
    controllers.push(
      add(gui, data, 'gridSize', 0, 100)
        .step(1)
        .name('Rows/Columns')
    );
    controllers.push(
      add(gui, data, 'gridGap', 0, 10).step(.1)
      .name('Grip gap')
    );
    controllers.push(
      add(gui, data, 'colorLibrary', data.colorLibraryNames).name(
        'Color library'
      )
      // .onChange(resetActiveSwatch)
      // .onChange(addColorSwatches)
    );
    controllers.push(add(gui, data, 'fillTriangles').name('Fill triangles'));
    controllers.push(add(gui, data, 'hatchLines').name('Add hatch lines'));
    controllers.push(
      add(gui, data, 'hatchLineLayers', 0, 5)
        .step(1)
        .name('# of line layers')
    );
    controllers.push(
      add(gui, data, 'minimumAngle', 0, 30)
        .step(1)
        .name('Minimum angle')
    );
    controllers.push(
      add(gui, data, 'distortion', 0, 10)
        .step(1)
        .name('Distortion')
    );
  }

  function add(gui, ...args) {
    return gui.add(...args).onChange(render);
  }

  function render() {
    manager.render();
  }
})();
