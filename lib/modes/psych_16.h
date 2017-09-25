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

 function: 16kHz settings

 ********************************************************************/

/* tonal masking curve level adjustments *************************/
static const vp_adjblock _vp_tonemask_adj_16[5]={
  /* adjust for mode zero */
  /* 63     125     250     500       1     2     4     8    16 */
  {{-16,-16,-16,-16,-16,-16,-10, -8, -4, 0, 0, 0, 0, 0, 0, 0, 0}}, /* -2 */
  {{-16,-16,-16,-16,-16,-16,-10, -8, -6,-2, 0, 0, 0, 0, 0, 0, 0}}, /* -1 */
  {{-16,-16,-16,-16,-16,-16,-10, -8, -6,-4, 0, 0, 0, 0, 0, 0, 0}}, /* 0.5 */
  {{-20,-20,-20,-20,-20,-16,-10,-10, -8,-6,-2,-2, 0, 0, 0, 0, 0}}, /*  5 */
  {{-30,-30,-30,-30,-30,-26,-20,-10, -8,-6,-2,-2, 0, 0, 0, 0, 0}}, /* 10 */
};

/* noise bias */
static const noise3 _psy_noisebias_16_short[5]={
  /*  63     125     250     500      1k       2k      4k      8k     16k*/
  {{{-15,-15,-15,-15,-15,-10,-10, -5,  4, 10, 10, 10, 10, 12, 12, 14, 20},
    {-12,-12,-12,-12,-12, -7, -7, -2,  3,  3,  4,  5,  6,  7,  8,  8, 15},
    {-30,-30,-30,-30,-30,-24,-20,-14,-10, -6, -8, -8, -6, -6, -6, -6, -6}}},

  {{{-15,-15,-15,-15,-15,-10,-10, -5,  4, 10, 10, 10, 10, 12, 12, 14, 20},
    {-15,-15,-15,-15,-15,-10,-10, -5,  0,  0,  4,  5,  5,  6,  8,  8, 15},
    {-30,-30,-30,-30,-30,-24,-20,-14,-10, -6, -8, -8, -6, -6, -6, -6, -6}}},

  {{{-15,-15,-15,-15,-15,-10,-10, -5,  4,  6,  6,  6,  6,  8, 10, 12, 20},
    {-15,-15,-15,-15,-15,-15,-15,-10, -5, -5, -5,  4,  5,  6,  8,  8, 15},
    {-30,-30,-30,-30,-30,-24,-20,-14,-10,-10,-10,-10,-10,-10,-10,-10,-10}}},

  {{{-15,-15,-15,-15,-15,-12,-10, -8,  0,  2,  4,  4,  5,  5,  5,  8, 12},
    {-20,-20,-20,-20,-16,-12,-20,-14,-10,-10, -8,  0,  0,  0,  0,  2,  5},
    {-30,-30,-30,-30,-26,-26,-26,-26,-26,-26,-26,-26,-26,-24,-20,-20,-20}}},

  {{{-15,-15,-15,-15,-15,-12,-10, -8, -5, -5, -5, -5, -5,  0,  0,  0,  6},
    {-30,-30,-30,-30,-26,-22,-20,-14,-12,-12,-10,-10,-10,-10,-10,-10, -6},
    {-30,-30,-30,-30,-26,-26,-26,-26,-26,-26,-26,-26,-26,-24,-20,-20,-20}}},
};

static const noise3 _psy_noisebias_16_impulse[5]={
  /*  63     125     250     500      1k       2k      4k      8k     16k*/
  {{{-15,-15,-15,-15,-15,-10,-10, -5,  4, 10, 10, 10, 10, 12, 12, 14, 20},
    {-12,-12,-12,-12,-12, -7, -7, -2,  3,  3,  4,  5,  6,  7,  8,  8, 15},
    {-30,-30,-30,-30,-30,-24,-20,-14,-10, -6, -8, -8, -6, -6, -6, -6, -6}}},

  {{{-15,-15,-15,-15,-15,-10,-10, -5,  4, 10, 10, 10, 10, 12, 12, 14, 20},
    {-15,-15,-15,-15,-15,-10,-10, -5,  0,  0,  4,  5,  5,  6,  8,  8, 15},
    {-30,-30,-30,-30,-30,-24,-20,-14,-10, -6, -8, -8, -6, -6, -6, -6, -6}}},

  {{{-15,-15,-15,-15,-15,-10,-10, -5,  4,  4,  4,  4,  5,  5,  6,  8, 15},
    {-15,-15,-15,-15,-15,-15,-15,-10, -5, -5, -5,  0,  0,  0,  0,  4, 10},
    {-30,-30,-30,-30,-30,-24,-20,-14,-10,-10,-10,-10,-10,-10,-10,-10,-10}}},

  {{{-15,-15,-15,-15,-15,-12,-10, -8,  0,  0,  0,  0,  0,  0,  0,  4, 10},
    {-20,-20,-20,-20,-16,-12,-20,-14,-10,-10,-10,-10,-10,-10,-10, -7, -5},
    {-30,-30,-30,-30,-26,-26,-26,-26,-26,-26,-26,-26,-26,-24,-20,-20,-20}}},

  {{{-15,-15,-15,-15,-15,-12,-10, -8, -5, -5, -5, -5, -5,  0,  0,  0,  6},
    {-30,-30,-30,-30,-26,-22,-20,-18,-18,-18,-20,-20,-20,-20,-20,-20,-16},
    {-30,-30,-30,-30,-26,-26,-26,-26,-26,-26,-26,-26,-26,-24,-20,-20,-20}}},
};

static const noise3 _psy_noisebias_16[5]={
  /*  63     125     250     500      1k       2k      4k      8k     16k*/
  {{{-10,-10,-10,-10, -5, -5, -5,  0,  4,  6,  8,  8, 10, 10, 10, 14, 20},
    {-10,-10,-10,-10,-10, -5, -2, -2,  2,  2,  2,  4,  5,  6,  8,  8, 15},
    {-30,-30,-30,-30,-30,-24,-20,-14,-10, -6, -8, -8, -6, -6, -6, -6, -6}}},

  {{{-10,-10,-10,-10, -5, -5, -5,  0,  4,  6,  8,  8, 10, 10, 10, 14, 20},
    {-10,-10,-10,-10,-10, -5, -2, -2,  0,  0,  0,  4,  5,  6,  8,  8, 15},
    {-30,-30,-30,-30,-30,-24,-20,-14,-10, -6, -8, -8, -6, -6, -6, -6, -6}}},

  {{{-10,-10,-10,-10, -5, -5, -5,  0,  4,  6,  6,  6,  6,  8, 10, 12, 20},
    {-15,-15,-15,-15,-15,-10, -5, -5,  0,  0,  0,  4,  5,  6,  8,  8, 15},
    {-30,-30,-30,-30,-30,-24,-20,-14,-10, -6, -8, -8, -6, -6, -6, -6, -6}}},

  {{{-15,-15,-15,-15,-15,-12,-10, -8,  0,  2,  4,  4,  5,  5,  5,  8, 12},
    {-20,-20,-20,-20,-16,-12,-20,-10, -5, -5,  0,  0,  0,  0,  0,  2,  5},
    {-30,-30,-30,-30,-26,-26,-26,-26,-26,-26,-26,-26,-26,-24,-20,-20,-20}}},

  {{{-15,-15,-15,-15,-15,-12,-10, -8, -5, -5, -5, -5, -5,  0,  0,  0,  6},
    {-30,-30,-30,-30,-26,-22,-20,-14,-12,-12,-10,-10,-10,-10,-10,-10, -6},
    {-30,-30,-30,-30,-26,-26,-26,-26,-26,-26,-26,-26,-26,-24,-20,-20,-20}}},
};

static const noiseguard _psy_noiseguards_16[4]={
  {10,10,-1},
  {10,10,-1},
  {20,20,-1},
  {20,20,-1},
};

/* ath ****************/
static const int _psy_ath_floater_16[5]={
  -100,-100,-100,-100,-105,
};
static const int _psy_ath_abs_16[5]={
  -130,-130,-130,-130,-140,
};

/* stereo mode by base quality level */
static const adj_stereo _psy_stereo_modes_16[5]={
  /*  0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  */
  {{  4,  4,  4,  3,  3,  3,  3,  3,  3,  3,  3,  3,  3,  3,  3},
   {  7,  7,  7,  7,  7,  7,  7,  7,  6,  6,  5,  5,  5,  4,  4},
   {  2,  2,  2,  2,  2,  2,  2,  2,  2,  2,  2,  3,  3,  4,  4},
   { 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99}},
  {{  4,  4,  4,  3,  3,  3,  3,  3,  3,  3,  3,  3,  3,  3,  3},
   {  7,  7,  6,  6,  6,  6,  6,  6,  5,  5,  5,  4,  4,  4,  4},
   {  2,  2,  2,  2,  2,  2,  2,  2,  2,  2,  2,  3,  3,  4,  4},
   { 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99}},
  {{  4,  4,  4,  3,  3,  3,  3,  3,  3,  3,  3,  3,  3,  3,  3},
   {  6,  5,  4,  4,  4,  4,  4,  4,  4,  4,  4,  4,  4,  4,  4},
   {  2,  2,  2,  2,  2,  2,  2,  2,  2,  3,  4,  4,  4,  4,  4},
   { 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99}},
  {{  3,  3,  3,  3,  3,  3,  3,  3,  3,  3,  3,  3,  3,  3,  3},
   {  5,  4,  3,  3,  3,  3,  3,  3,  3,  3,  3,  3,  3,  3,  3},
   {  4,  4,  4,  4,  4,  4,  4,  4,  4,  4,  4,  4,  4,  4,  4},
   { 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99}},
  {{  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0},
   {  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0},
   {  8,  8,  8,  8,  8,  8,  8,  8,  8,  8,  8,  8,  8,  8,  8},
   { 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99}},
};

/* tone master attenuation by base quality mode and bitrate tweak */
static const att3 _psy_tone_masteratt_16[5]={
  {{ 30,  25,  12},  0,   0},  /* -2 */
  {{ 30,  25,  12},  0,   0},  /* -1 */
  {{ 25,  23,  12},  0,   0},  /* 0.5 */
  {{ 20,  12,   0},  0,   0},  /*  5 */
  {{ 15,   0, -14},  0,   0},  /* 10 */
};

/* lowpass by mode **************/
static const double _psy_lowpass_16[5]={6.,6.5,8,30.,99.};

/* noise normalization **********/
static const int _noise_start_16[4]={ 256,256,256,9999 };

static const int _noise_part_16[4]={ 8,8,8,8 };

static const double _noise_thresh_16[4]={ .3,.4,.5,.5 };
