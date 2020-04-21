import apiFetch from '../util/apiFetch';

export default class ServiceCategoryService {
  static instance = null;
  static getInstance() {
    if (ServiceCategoryService.instance === null) {
      ServiceCategoryService.instance = new ServiceCategoryService();
    }
    return this.instance;
  }
  findServiceCategoryById = categoryId =>
    apiFetch(`/api/categories/${categoryId}`).then(response => response.json());

  findAllServiceCategories = limit =>
    apiFetch(limit ? `/api/categories?limit=${limit}` : '/api/categories').then(
      response => response.json()
    );

  createServiceCategory = serviceCategory =>
    apiFetch('/api/categories', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(serviceCategory),
    }).then(response => response.json());

  updateServiceCategory = (id, serviceCategory) =>
    apiFetch(`/api/categories/${id}`, {
      method: 'PUT',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(serviceCategory),
    }).then(response => response.json());

  deleteServiceCategory = id =>
    apiFetch(`/api/categories/${id}`, { method: 'DELETE' });

  filterServiceCategory = () => {};

  paginate = () => {};
}
