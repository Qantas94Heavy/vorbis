/********************************************************************
 *                                                                  *
 * THIS FILE IS PART OF THE OggVorbis SOFTWARE CODEC SOURCE CODE.   *
 * USE, DISTRIBUTION AND REPRODUCTION OF THIS LIBRARY SOURCE IS     *
 * GOVERNED BY A BSD-STYLE SOURCE LICENSE INCLUDED WITH THIS SOURCE *
 * IN 'COPYING'. PLEASE READ THESE TERMS BEFORE DISTRIBUTING.       *
 *                                                                  *
 * THE OggVorbis SOURCE CODE IS (C) COPYRIGHT 1994-2009             *
 * by the Xiph.Org Foundation http://www.xiph.org/                  *
 *                                                                  *
 ********************************************************************

 function: 11kHz settings

 ********************************************************************/

static const double _psy_lowpass_11[3]={4.5,5.5,30.,};

static const att3 _psy_tone_masteratt_11[3]={
  {{ 30,  25,  12},  0,   0},  /* 0 */
  {{ 30,  25,  12},  0,   0},  /* 0 */
  {{ 20,   0, -14},  0,   0}, /* 0 */
};

static const vp_adjblock _vp_tonemask_adj_11[3]={
  /* adjust for mode zero */
  /* 63     125     250     500     1     2     4     8    16 */
  {{-20,-20,-20,-20,-20,-16,-10, 0, 0, 0, 0,10, 2, 0,99,99,99}}, /* 0 */
  {{-20,-20,-20,-20,-20,-16,-10, 0, 0, 0, 0, 5, 0, 0,99,99,99}}, /* 1 */
  {{-20,-20,-20,-20,-20,-16,-10, 0, 0, 0, 0, 0, 0, 0,99,99,99}}, /* 2 */
};


static const noise3 _psy_noisebias_11[3]={
  /*  63     125     250     500      1k       2k      4k      8k     16k*/
  {{{-10,-10,-10,-10, -5, -5, -5,  0,  4, 10, 10, 12, 12, 12, 99, 99, 99},
    {-15,-15,-15,-15,-10,-10, -5,  0,  0,  4,  4,  5,  5, 10, 99, 99, 99},
    {-30,-30,-30,-30,-30,-24,-20,-14,-10, -6, -8, -8, -6, -6, 99, 99, 99}}},

  {{{-10,-10,-10,-10, -5, -5, -5,  0,  4, 10, 10, 12, 12, 12, 99, 99, 99},
    {-15,-15,-15,-15,-10,-10, -5, -5, -5,  0,  0,  0,  0,  0, 99, 99, 99},
    {-30,-30,-30,-30,-30,-24,-20,-14,-10, -6, -8, -8, -6, -6, 99, 99, 99}}},

  {{{-15,-15,-15,-15,-15,-12,-10, -8,  0,  2,  4,  4,  5,  5, 99, 99, 99},
    {-30,-30,-30,-30,-26,-22,-20,-14,-12,-12,-10,-10,-10,-10, 99, 99, 99},
    {-30,-30,-30,-30,-26,-26,-26,-26,-26,-26,-26,-26,-26,-24, 99, 99, 99}}},
};

/* tone master attenuation by base quality mode and bitrate tweak */
static const att3 _psy_tone_masteratt_11[4]={
  {{ 31,  25,  13},  0,   0},  /* -2 */
  {{ 30,  25,  12},  0,   0},  /* -1 */
  {{ 30,  25,  12},  0,   0},  /*  0 */
  {{ 20,   0, -14},  0,   0},  /* 10 */
};

/* lowpass by mode **************/
static const double _psy_lowpass_11[4]={4.,4.5,5.5,30.,};

/* noise normalization **********/
static const double _noise_thresh_11[3]={ .3,.3,.5 };
