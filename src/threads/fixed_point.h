#ifndef FIXED_POINT_H
#define FIXED_POINT_H

#include <stdint.h>

#define F (1 << 14)  

typedef struct {
    int32_t value;
} fixed_point;

static inline fixed_point int_to_fp(int n) {
    return (fixed_point){ n * F };
}


static inline int fp_to_int(fixed_point x) {
    return x.value / F;
}

static inline int fp_to_int_nearest(fixed_point x) {
    return (x.value >= 0) ? (x.value + F / 2) / F : (x.value - F / 2) / F;
}


static inline fixed_point fp_add(fixed_point x, fixed_point y) {
    return (fixed_point){ x.value + y.value };
}

static inline fixed_point fp_sub(fixed_point x, fixed_point y) {
    return (fixed_point){ x.value - y.value };
}


static inline fixed_point fp_add_int(fixed_point x, int n) {
    return (fixed_point){ x.value + n * F };
}


static inline fixed_point fp_sub_int(fixed_point x, int n) {
    return (fixed_point){ x.value - n * F };
}


static inline fixed_point fp_mul(fixed_point x, fixed_point y) {
    return (fixed_point){ ((int64_t)x.value * y.value) / F };
}

static inline fixed_point fp_mul_int(fixed_point x, int n) {
    return (fixed_point){ x.value * n };
}


static inline fixed_point fp_div(fixed_point x, fixed_point y) {
    return (fixed_point){ ((int64_t)x.value * F) / y.value };
}


static inline fixed_point fp_div_int(fixed_point x, int n) {
    return (fixed_point){ x.value / n };
}

#endif 
