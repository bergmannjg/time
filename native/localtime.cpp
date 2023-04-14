#include <string>
#include <time.h>
#include <lean/lean.h>

static inline lean_object * lean_mk_tuple2(lean_object * a, lean_object * b) {
  lean_object* tuple = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(tuple, 0, a);
  lean_ctor_set(tuple, 1, b);
  return tuple;
}

extern "C" LEAN_EXPORT lean_object* lean_get_current_timezone () {
    time_t result;
    struct tm res;
    result = time(NULL);
    int64_t gmtoff = 0;
    int64_t isdst = 0;
    char const * tm_zone = 0;
    if (result && localtime_r(&result, &res)) {
        gmtoff = res.tm_gmtoff;
        isdst = res.tm_isdst;
        tm_zone = res.tm_zone;
    }
    return lean_io_result_mk_ok(lean_mk_tuple2(lean_int64_to_int(gmtoff), lean_mk_tuple2(lean_int_to_int(isdst), lean_mk_string(tm_zone))));
}

extern "C" LEAN_EXPORT lean_object* lean_clock_gettime () {
    time_t tv_sec = 0;
    uint32_t tv_nsec = 0;
    struct timespec res;
    if (0 == clock_gettime(CLOCK_REALTIME, &res)) {
        tv_sec = res.tv_sec;
        tv_nsec = (uint32_t)res.tv_nsec;
    }
    return lean_io_result_mk_ok(lean_mk_tuple2(lean_int64_to_int(tv_sec), lean_int_to_int(tv_nsec)));
}
