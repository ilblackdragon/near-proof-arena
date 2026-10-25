
/* Export diagnostic scalar policy for the Rust bridge commitments. */
int near_sis_secure(size_t rank,size_t width,double norm);
int near_sis_secure(size_t rank,size_t width,double norm) { return screen_sis_secure(rank,width,norm); }
