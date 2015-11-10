#ifndef OSL_WRAPPER
#define OSL_WRAPPER

#include <clay/array.h>
#include <clay/list.h>

char *clay_array_string(clay_array_p array);
char *clay_list_string(clay_list_p list);
int clay_list_equal(clay_list_p l1, clay_list_p l2);


template <typename T, T *(creator)(), void (deleter)(T *),
          T *(cloner)(T *), int (equality)(T *, T *), char *(printer)(T *)>
class OSLContainer {
public:
  OSLContainer() {
    object = creator();
  }

  OSLContainer(T *other) {
    object = other;
  }

  static OSLContainer copy(T *other) {
    T *clone = cloner(other);
    return OSLContainer(clone);
  }

  OSLContainer(const OSLContainer &other) {
    object = cloner(other.object);
  }

  OSLContainer(T &&other) {
    object = other.object;
    other.object = nullptr;
  }

  ~OSLContainer() {
    deleter(object);
  }

  OSLContainer &operator = (const OSLContainer &other) {
    deleter(object);
    object = cloner(other.object);
    return *this;
  }

  bool operator == (const OSLContainer &other) const {
    return equality(object, other.object);
  }

  bool operator != (const OSLContainer &other) const {
    return !equality(object, other.object);
  }

  operator T *() {
    return object;
  }

  operator T &() {
    return *object;
  }

  friend std::ostream &operator <<(std::ostream &out, const OSLContainer &container) {
    char *cstring = printer(container.object);
    out << cstring;
    free(cstring);
    return out;
  }

private:
  T *object;
};

typedef OSLContainer<clay_array_t, clay_array_malloc, clay_array_free, clay_array_clone, clay_array_equal, clay_array_string> ClayArray;
typedef OSLContainer<clay_list_t, clay_list_malloc, clay_list_free, clay_list_clone, clay_list_equal, clay_list_string> ClayList;

#endif // OSL_WRAPPER
