package services;

import models.Service;
import models.ServiceCategory;
import repositories.ServiceCategoryRepository;
import repositories.ServiceQuestionRepository;
import repositories.ServiceRepository;

import java.util.List;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.web.bind.annotation.CrossOrigin;
import org.springframework.web.bind.annotation.DeleteMapping;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.PathVariable;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.PutMapping;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.RestController;

@RestController
@CrossOrigin(origins = "*")
public class ServiceCategoryService {
    @Autowired
    ServiceCategoryRepository serviceCategoryRepository;
    @Autowired
    ServiceRepository serviceRepository;
    @Autowired
    ServiceQuestionRepository serviceQuestionRepository;

    @GetMapping("/api/categories")
    public List<ServiceCategory> findAllServiceCategories(
            @RequestParam(name = "limit", required = false) Integer limit) {
        List<ServiceCategory> categories = serviceCategoryRepository.findAllServiceCategories();
        if (limit != null && categories.size() > limit) {
            return categories.subList(0, limit);
        }
        return categories;
    }

    @GetMapping("/api/categories/{serviceCategoryId}")
    public ServiceCategory findServiceCategoryById(@PathVariable("serviceCategoryId") Integer id) {
        return serviceCategoryRepository.findServiceCategoryById(id);
    }

    @GetMapping("/api/categories/{serviceCategoryId}/services")
    public List<Service> findServicesByServiceCategory(@PathVariable("serviceCategoryId") Integer id) {
        ServiceCategory serviceCategory = serviceCategoryRepository.findServiceCategoryById(id);
        return serviceCategory.getServices();
    }

    @PostMapping("/api/categories/{serviceCategoryId}/services/{serviceId}")
    public ServiceCategory createServiceRelationship(@PathVariable("serviceCategoryId") Integer category_id,
            @PathVariable("serviceId") Integer service_id) {
        ServiceCategory serviceCategory = serviceCategoryRepository.findServiceCategoryById(category_id);
        Service service = serviceRepository.findServiceById(service_id);
        List<Service> categoryRelations = serviceCategory.getServices();
        List<ServiceCategory> serviceRelations = service.getServiceCategories();
        if (!categoryRelations.contains(service)) {
            categoryRelations.add(service);
            serviceCategory.setServices(categoryRelations);
            serviceRelations.add(serviceCategory);
            service.setServiceCategories(serviceRelations);
        }
        serviceRepository.save(service);
        return serviceCategoryRepository.save(serviceCategory);
    }

    @DeleteMapping("/api/categories/{serviceCategoryId}/services/{serviceId}")
    public ServiceCategory deleteServiceRelationship(@PathVariable("serviceCategoryId") Integer category_id,
            @PathVariable("serviceId") Integer service_id) {
        ServiceCategory serviceCategory = serviceCategoryRepository.findServiceCategoryById(category_id);
        Service service = serviceRepository.findServiceById(service_id);
        List<Service> categoryRelations = serviceCategory.getServices();
        List<ServiceCategory> serviceRelations = service.getServiceCategories();
        if (categoryRelations.contains(service)) {
            categoryRelations.remove(service);
            serviceCategory.setServices(categoryRelations);
            serviceRelations.remove(serviceCategory);
            service.setServiceCategories(serviceRelations);
        }
        serviceRepository.save(service);
        return serviceCategoryRepository.save(serviceCategory);
    }

    @PostMapping("/api/categories")
    public ServiceCategory createServiceCategory(@RequestBody ServiceCategory serviceCategory) {
        return serviceCategoryRepository.save(serviceCategory);
    }

    @PutMapping("/api/categories/{serviceCategoryId}")
    public ServiceCategory updateServiceCategory(@PathVariable("serviceCategoryId") Integer id,
            @RequestBody ServiceCategory serviceUpdates) {
        ServiceCategory serviceCategory = serviceCategoryRepository.findServiceCategoryById(id);
        serviceCategory.setTitle(serviceUpdates.getTitle());
        serviceCategory.setDescription(serviceUpdates.getDescription());
        serviceCategory.setServices(serviceUpdates.getServices());
        serviceCategory.setPopularity(serviceUpdates.getPopularity());
        return serviceCategoryRepository.save(serviceCategory);
    }

    @DeleteMapping("/api/categories/{serviceCategoryId}")
    public void deleteServiceCategory(@PathVariable("serviceCategoryId") Integer id) {
        serviceCategoryRepository.deleteById(id);
    }
}
