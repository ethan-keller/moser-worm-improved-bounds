#ifndef MOSER_LOWER_API_H
#define MOSER_LOWER_API_H

/* Public entrypoints in libraries compiled with hidden default visibility. */
#define MOSER_LOWER_API __attribute__((visibility("default")))

#endif
