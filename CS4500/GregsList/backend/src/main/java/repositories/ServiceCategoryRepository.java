package repositories;

import java.util.List;

import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.CrudRepository;
import org.springframework.data.repository.query.Param;

import models.ServiceCategory;

/**
 * used for interfacing with the service category SQL database.
 */
public interface ServiceCategoryRepository extends CrudRepository<ServiceCategory, Integer> {

  @Query(value = "SELECT serviceCategory FROM ServiceCategory serviceCategory ORDER BY popularity DESC")
  public List<ServiceCategory> findAllServiceCategories();

  @Query(value = "SELECT serviceCategory FROM ServiceCategory serviceCategory WHERE serviceCategory.id=:id")
  public ServiceCategory findServiceCategoryById(@Param("id") Integer id);
}