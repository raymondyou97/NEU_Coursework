package utils;

import org.springframework.data.domain.PageRequest;
import org.springframework.data.domain.Pageable;

public class PaginationUtils {
  public static Pageable getPageable(Integer page, Integer count) {
    if (page == null) {
      page = 0;
    }

    if (count == null) {
      count = 10;
    }

    return PageRequest.of(page, count);
  }
}
