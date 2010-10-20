#include <unistd.h>
#include <stdio.h>
#include <string.h>
#include <glib-object.h>

static GType TEST_TYPE_OBJECT;

static GType
test_pobject_register_type ()
{
  static const GTypeInfo info = {
    sizeof (GObjectClass),			/* class_size     */
    (GBaseInitFunc) NULL,	/* base_init      */
    (GBaseFinalizeFunc) NULL,			/* base_finalize  */
    (GClassInitFunc) NULL,	/* class_init     */
    (GClassFinalizeFunc) NULL,		 	/* class_finalize */
    NULL,					/* class_data     */
    sizeof (GObject),			/* instance_size  */
    0,						/* n_prelocs      */
    (GInstanceInitFunc) NULL			/* instance_init  */
  };

  return g_type_register_static (G_TYPE_OBJECT, "TestPObject", &info, 0);
}

static GType
test_object_register_type ()
{
  static const GTypeInfo info = {
    sizeof (GObjectClass),			/* class_size     */
    (GBaseInitFunc) NULL,			/* base_init      */
    (GBaseFinalizeFunc) NULL,			/* base_finalize  */
    (GClassInitFunc) NULL,	/* class_init     */
    (GClassFinalizeFunc) NULL,		 	/* class_finalize */
    NULL,					/* class_data     */
    sizeof (GObject),			/* instance_size  */
    0,						/* n_prelocs      */
    (GInstanceInitFunc) NULL			/* instance_init  */
  };

  return g_type_register_static (test_pobject_register_type(), "TestObject", &info, 0);
}

static void *
thread (void *data)
{
  g_object_new (TEST_TYPE_OBJECT, NULL);
  return NULL;
}

int
main (int argc, char *argv[])
{
  g_thread_init (NULL);
  g_type_init ();

  TEST_TYPE_OBJECT = test_object_register_type();

  g_thread_create (thread, NULL, TRUE, NULL);
  thread (NULL);

  return 0;
}
