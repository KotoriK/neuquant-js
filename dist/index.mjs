/**
 * NeuQuant Neural-Network Quantization Algorithm
 *
 * Copyright (c) 1994 Anthony Dekker
 *
 * See "Kohonen neural networks for optimal colour quantization" in "Network:
 * Computation in Neural Systems" Vol. 5 (1994) pp 351-367. for a discussion of
 * the algorithm.
 *
 * See also http://members.ozemail.com.au/~dekker/NEUQUANT.HTML
 *
 * Any party obtaining a copy of these files from the author, directly or
 * indirectly, is granted, free of charge, a full and unrestricted irrevocable,
 * world-wide, paid up, royalty-free, nonexclusive right and license to deal in
 * this software and documentation files (the "Software"), including without
 * limitation the rights to use, copy, modify, merge, publish, distribute,
 * sublicense, and/or sell copies of the Software, and to permit persons who
 * receive copies from any such party to do so, with the only requirement being
 * that this copyright notice remain intact.
 *
 * Copyright (c) 2012 Johan Nordberg (JavaScript port)
 * Copyright (c) 2014 Devon Govett (JavaScript port)
 */

var prime1 = 499;
var prime2 = 491;
var prime3 = 487;
var prime4 = 503;
var maxprime = Math.max(prime1, prime2, prime3, prime4);
var minpicturebytes = 3 * maxprime;
var defaults = {
  ncycles: 100,
  netsize: 256,
  samplefac: 10
};
var assign = function assign(target) {
  for (var i = 1, l = arguments.length; i < l; i++) {
    var nextSource = arguments[i];
    if (nextSource != null) {
      for (var nextKey in nextSource) {
        if (Object.prototype.hasOwnProperty.call(nextSource, nextKey)) {
          target[nextKey] = nextSource[nextKey];
        }
      }
    }
  }
  return target;
};
var NeuQuant = /*#__PURE__*/function () {
  function NeuQuant(pixels, options) {
    assign(this, defaults, {
      pixels: pixels
    }, options);
    if (this.netsize < 4 || this.netsize > 256) {
      throw new Error('Color count must be between 4 and 256');
    }
    if (this.samplefac < 1 || this.samplefac > 30) {
      throw new Error('Sampling factor must be between 1 and 30');
    }
    this.maxnetpos = this.netsize - 1;
    this.netbiasshift = 4;
    this.intbiasshift = 16;
    this.intbias = 1 << this.intbiasshift;
    this.gammashift = 10;
    this.gamma = 1 << this.gammashift;
    this.betashift = 10;
    this.beta = this.intbias >> this.betashift;
    this.betagamma = this.beta * this.gamma;
    this.initrad = this.netsize >> 3;
    this.radiusbiasshift = 6;
    this.radiusbias = 1 << this.radiusbiasshift;
    this.initradius = this.initrad * this.radiusbias;
    this.radiusdec = 30;
    this.alphabiasshift = 10;
    this.initalpha = 1 << this.alphabiasshift;
    this.radbiasshift = 8;
    this.radbias = 1 << this.radbiasshift;
    this.alpharadbshift = this.alphabiasshift + this.radbiasshift;
    this.alpharadbias = 1 << this.alpharadbshift;
    this.network = [];
    this.netindex = new Uint32Array(256);
    this.bias = new Uint32Array(this.netsize);
    this.freq = new Uint32Array(this.netsize);
    this.radpower = new Uint32Array(this.netsize >> 3);
    for (var i = 0, l = this.netsize; i < l; i++) {
      var v = (i << this.netbiasshift + 8) / this.netsize;
      this.network[i] = new Float64Array([v, v, v, 0]);
      this.freq[i] = this.intbias / this.netsize;
      this.bias[i] = 0;
    }
  }
  var _proto = NeuQuant.prototype;
  _proto.unbiasnet = function unbiasnet() {
    for (var i = 0, l = this.netsize; i < l; i++) {
      this.network[i][0] >>= this.netbiasshift;
      this.network[i][1] >>= this.netbiasshift;
      this.network[i][2] >>= this.netbiasshift;
      this.network[i][3] = i;
    }
  };
  _proto.altersingle = function altersingle(alpha, i, b, g, r) {
    this.network[i][0] -= alpha * (this.network[i][0] - b) / this.initalpha;
    this.network[i][1] -= alpha * (this.network[i][1] - g) / this.initalpha;
    this.network[i][2] -= alpha * (this.network[i][2] - r) / this.initalpha;
  };
  _proto.alterneigh = function alterneigh(radius, i, b, g, r) {
    var lo = Math.abs(i - radius);
    var hi = Math.min(i + radius, this.netsize);
    var j = i + 1;
    var k = i - 1;
    var m = 1;
    while (j < hi || k > lo) {
      var a = this.radpower[m++];
      if (j < hi) {
        var p = this.network[j++];
        p[0] -= a * (p[0] - b) / this.alpharadbias;
        p[1] -= a * (p[1] - g) / this.alpharadbias;
        p[2] -= a * (p[2] - r) / this.alpharadbias;
      }
      if (k > lo) {
        var _p = this.network[k--];
        _p[0] -= a * (_p[0] - b) / this.alpharadbias;
        _p[1] -= a * (_p[1] - g) / this.alpharadbias;
        _p[2] -= a * (_p[2] - r) / this.alpharadbias;
      }
    }
  };
  _proto.contest = function contest(b, g, r) {
    var bestd = ~(1 << 31);
    var bestbiasd = bestd;
    var bestpos = -1;
    var bestbiaspos = bestpos;
    for (var i = 0, l = this.netsize; i < l; i++) {
      var n = this.network[i];
      var dist = Math.abs(n[0] - b) + Math.abs(n[1] - g) + Math.abs(n[2] - r);
      if (dist < bestd) {
        bestd = dist;
        bestpos = i;
      }
      var biasdist = dist - (this.bias[i] >> this.intbiasshift - this.netbiasshift);
      if (biasdist < bestbiasd) {
        bestbiasd = biasdist;
        bestbiaspos = i;
      }
      var betafreq = this.freq[i] >> this.betashift;
      this.freq[i] -= betafreq;
      this.bias[i] += betafreq << this.gammashift;
    }
    this.freq[bestpos] += this.beta;
    this.bias[bestpos] -= this.betagamma;
    return bestbiaspos;
  };
  _proto.inxbuild = function inxbuild() {
    var previouscol = 0;
    var startpos = 0;
    for (var i = 0, l = this.netsize; i < l; i++) {
      var p = this.network[i];
      var q = null;
      var smallpos = i;
      var smallval = p[1];
      for (var j = i + 1; j < l; j++) {
        q = this.network[j];
        if (q[1] < smallval) {
          smallpos = j;
          smallval = q[1];
        }
      }
      q = this.network[smallpos];
      if (i !== smallpos) {
        var _ref = [q[0], p[0]];
        p[0] = _ref[0];
        q[0] = _ref[1];
        var _ref2 = [q[1], p[1]];
        p[1] = _ref2[0];
        q[1] = _ref2[1];
        var _ref3 = [q[2], p[2]];
        p[2] = _ref3[0];
        q[2] = _ref3[1];
        var _ref4 = [q[3], p[3]];
        p[3] = _ref4[0];
        q[3] = _ref4[1];
      }
      if (smallval !== previouscol) {
        this.netindex[previouscol] = startpos + i >> 1;
        for (var _j = previouscol + 1; _j < smallval; _j++) {
          this.netindex[_j] = i;
        }
        previouscol = smallval;
        startpos = i;
      }
    }
    this.netindex[previouscol] = startpos + this.maxnetpos >> 1;
    for (var _i = previouscol + 1; _i < 256; _i++) {
      this.netindex[_i] = this.maxnetpos;
    }
  };
  _proto.learn = function learn() {
    var lengthcount = this.pixels.length;
    var alphadec = 30 + (this.samplefac - 1) / 3;
    var samplepixels = lengthcount / (3 * this.samplefac);
    var delta = samplepixels / this.ncycles | 0;
    var alpha = this.initalpha;
    var radius = this.initradius;
    var rad = radius >> this.radiusbiasshift;
    if (rad <= 1) {
      rad = 0;
    }
    for (var i = 0; i < rad; i++) {
      this.radpower[i] = alpha * ((rad * rad - i * i) * this.radbias / (rad * rad));
    }
    var step;
    if (lengthcount < minpicturebytes) {
      this.samplefac = 1;
      step = 3;
    } else if (lengthcount % prime1 !== 0) {
      step = 3 * prime1;
    } else if (lengthcount % prime2 !== 0) {
      step = 3 * prime2;
    } else if (lengthcount % prime3 !== 0) {
      step = 3 * prime3;
    } else {
      step = 3 * prime4;
    }
    var pix = 0;
    for (var _i2 = 0; _i2 < samplepixels;) {
      var b = (this.pixels[pix] & 0xff) << this.netbiasshift;
      var g = (this.pixels[pix + 1] & 0xff) << this.netbiasshift;
      var r = (this.pixels[pix + 2] & 0xff) << this.netbiasshift;
      var j = this.contest(b, g, r);
      this.altersingle(alpha, j, b, g, r);
      if (rad !== 0) {
        this.alterneigh(rad, j, b, g, r);
      }
      pix += step;
      if (pix >= lengthcount) {
        pix -= lengthcount;
      }
      if (delta === 0) {
        delta = 1;
      }
      if (++_i2 % delta === 0) {
        alpha -= alpha / alphadec;
        radius -= radius / this.radiusdec;
        rad = radius >> this.radiusbiasshift;
        if (rad <= 1) {
          rad = 0;
        }
        for (var k = 0; k < rad; k++) {
          this.radpower[k] = alpha * ((rad * rad - k * k) * this.radbias / (rad * rad));
        }
      }
    }
  };
  _proto.buildColorMap = function buildColorMap() {
    this.learn();
    this.unbiasnet();
    this.inxbuild();
  };
  _proto.getColorMap = function getColorMap() {
    var map = new Buffer(this.netsize * 3);
    var index = new Buffer(this.netsize);
    for (var i = 0, l = this.netsize; i < l; i++) {
      index[this.network[i][3]] = i;
    }
    for (var _i3 = 0, j = 0, k = 0, _l = this.netsize; _i3 < _l; _i3++) {
      k = index[_i3];
      map[j++] = this.network[k][0] & 0xff;
      map[j++] = this.network[k][1] & 0xff;
      map[j++] = this.network[k][2] & 0xff;
    }
    return map;
  };
  return NeuQuant;
}();

function findClosest(palette, r, g, b) {
  var minpos = 0;
  var mind = 256 * 256 * 256;
  for (var i = 0, l = palette.length; i < l;) {
    var dr = r - palette[i++];
    var dg = g - palette[i++];
    var db = b - palette[i];
    var d = dr * dr + dg * dg + db * db;
    var pos = i / 3 | 0;
    if (d < mind) {
      mind = d;
      minpos = pos;
    }
    i++;
  }
  return minpos;
}
function palette(pixels, options) {
  var nq = new NeuQuant(pixels, options);
  nq.buildColorMap();
  return nq.getColorMap();
}
function indexed(pixels, palette) {
  var indexed = new Buffer(pixels.length / 3);
  var memo = {};
  for (var i = 0, j = 0, l = pixels.length; i < l;) {
    var r = pixels[i++];
    var g = pixels[i++];
    var b = pixels[i++];
    var k = r << 16 | g << 8 | b;
    if (k in memo) {
      indexed[j++] = memo[k];
    } else {
      indexed[j++] = memo[k] = findClosest(palette, r, g, b);
    }
  }
  return indexed;
}
function quantize(pixels, options) {
  var p = palette(pixels, options);
  var i = indexed(pixels, p);
  return {
    palette: p,
    indexed: i
  };
}

export { indexed, palette, quantize };
//# sourceMappingURL=index.mjs.map
